/* Copyright (c) 2016, 2017                                               */
/*       Institute of Software, Chinese Academy of Sciences               */
/* This file is part of ROLL, a Regular Omega Language Learning library.  */
/* ROLL is free software: you can redistribute it and/or modify           */
/* it under the terms of the GNU General Public License as published by   */
/* the Free Software Foundation, either version 3 of the License, or      */
/* (at your option) any later version.                                    */

/* This program is distributed in the hope that it will be useful,        */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of         */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          */
/* GNU General Public License for more details.                           */

/* You should have received a copy of the GNU General Public License      */
/* along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

package roll.learner.nba.mldollar;

import java.util.List;

import automata.FiniteAutomaton;
import dk.brics.automaton.Automaton;
import dk.brics.automaton.BasicOperations;
import oracle.IntersectionCheck;
import roll.automata.DFA;
import roll.automata.NBA;
import roll.automata.operations.DFAOperations;
import roll.automata.operations.FDFAOperations;
import roll.automata.operations.NBAOperations;
import roll.learner.LearnerBase;
import roll.learner.LearnerDFA;
import roll.learner.LearnerType;
import roll.learner.dfa.table.LearnerMDFATableColumn;
import roll.learner.dfa.tree.LearnerDFATreeColumn;
import roll.main.Options;
import roll.main.inclusion.UtilInclusion;
import roll.oracle.MembershipOracle;
import roll.query.Query;
import roll.query.QuerySimple;
import roll.table.HashableValue;
import roll.util.Pair;
import roll.words.Alphabet;
import roll.words.Word;


public class LearnerNBAMLDollar extends LearnerBase<NBA>{
    
    private final int dollarLetter;
    private final LearnerDFA dfaLearner;
    private final Automaton nonUPWords;
    
    public LearnerNBAMLDollar(Options options, Alphabet alphabet
            , MembershipOracle<HashableValue> membershipOracle) {
        super(options, alphabet, membershipOracle);
        // we have to add a new letter '$' for DFA
        alphabet.addLetter(Alphabet.DOLLAR);
        dollarLetter = alphabet.indexOf(Alphabet.DOLLAR);
        Automaton allUPWords = UtilNBAMLDollar.getAllUPWords(alphabet, dollarLetter);
        nonUPWords = allUPWords.complement();
        MembershipOracleNBAMLDollar lDollarMembershipOracle = new MembershipOracleNBAMLDollar(membershipOracle, dollarLetter);
        if(options.structure.isTable()) {
            dfaLearner = new LearnerMDFATableColumn(options, alphabet, lDollarMembershipOracle);
        }else {
            dfaLearner = new LearnerDFATreeColumn(options, alphabet, lDollarMembershipOracle);
        }
    }

    @Override
    public LearnerType getLearnerType() {
        return LearnerType.NBA_MLDOLLAR;
    }
    
    @Override
    protected void initialize() {
        dfaLearner.startLearning();
        constructHypothesis();
    }

    public static Pair<Word, Word> getCounterexample(Alphabet alphabet, List<String> prefix, List<String> suffix) {
        int[] pre = new int[prefix.size()];
        for(int i = 0; i < pre.length; i ++) {
            pre[i] = alphabet.indexOf(prefix.get(i).charAt(0));
        }
        int[] suf = new int[suffix.size()];
        for(int i = 0; i < suf.length; i ++) {
            suf[i] = alphabet.indexOf(suffix.get(i).charAt(0));
        }
        return new Pair<>(alphabet.getArrayWord(pre), alphabet.getArrayWord(suf));
    }

    @Override
    protected void constructHypothesis() {
        
        Automaton dkAut;
        while(true) {
            // first check whether it is a subset of E*$E+
            DFA dfa = dfaLearner.getHypothesis();
            dkAut = DFAOperations.toDkDFA(dfa);
            Automaton dkAutInter = dkAut.intersection(nonUPWords);
            String counterexample = dkAutInter.getShortestExample(true);
            if (counterexample != null) {
                // there is some word not in E*$E+
                System.out.print("Wrong Form CE: ");
                System.out.println(counterexample);
                Word word = alphabet.getWordFromString(counterexample);
                Query<HashableValue> ceQuery = new QuerySimple<>(word, alphabet.getEmptyWord());
                ceQuery.answerQuery(getHashableValueBoolean(false));
                dfaLearner.refineHypothesis(ceQuery);
            } else {
                // DFA accepts a subset of E*$E+

                DFA testSaturation = dfaLearner.getHypothesis();
                Automaton satDk = DFAOperations.toDkDFA(testSaturation);
                Automaton dcSatDk = dollarComplement(satDk);

                Automaton satAsBuchi = UtilNBAMLDollar.dkDFAToBuchi(satDk);
                Automaton dcSatAsBuchi = UtilNBAMLDollar.dkDFAToBuchi(dcSatDk);
                

                NBA hypoNBA = NBAOperations.fromDkNBA(satAsBuchi, alphabet);
                NBA dcHypoNBA = NBAOperations.fromDkNBA(dcSatAsBuchi, alphabet);

                FiniteAutomaton rhyp = UtilInclusion.toRABITNBA(hypoNBA);
                FiniteAutomaton rtar = UtilInclusion.toRABITNBA(dcHypoNBA);

                IntersectionCheck checker = new IntersectionCheck(rhyp, rtar);
                boolean isEmpty = checker.checkEmptiness();

                if (!isEmpty) {
                    checker.computePath();
                    Pair<Word, Word> pair = getCounterexample(alphabet, checker.getPrefix(), checker.getSuffix());
                    Word prefix = pair.getLeft();
                    Word suffix = pair.getRight();

                    Query<HashableValue> ceQuery = new QuerySimple<>(prefix,suffix);
                    ceQuery.answerQuery(getHashableValueBoolean(false));
                    
                    options.log.println("Analyzing counterexample for DFA learner...");
                    Automaton result = FDFAOperations.buildDDollar(prefix, suffix);
                    String counterexampleStr = null;
                    DFA dfa1 = dfaLearner.getHypothesis();
                    Automaton dkAut1 = DFAOperations.toDkDFA(dfa1);
                    HashableValue answer = null;
                    if(answer == null) {
                        answer = membershipOracle.answerMembershipQuery(ceQuery);
                    }
                    if (answer.isAccepting()) {
                        counterexampleStr = result.minus(dkAut1).getShortestExample(true);
                    } else {
                        counterexampleStr = dkAut.intersection(result).getShortestExample(true);
                    }
                    
                    Word word = alphabet.getWordFromString(counterexampleStr);
                    Query<HashableValue> query = new QuerySimple<>(word, alphabet.getEmptyWord());
                    query.answerQuery(answer);
                    dfaLearner.refineHypothesis(query);
                    

                } else {
                    break;
                }
            }
        }
        // now we construct the NBA
    
        // dollar-complement automaton
        Automaton dcDkAut = dollarComplement(dkAut);
        Automaton dcDkAutAsBuchi = UtilNBAMLDollar.dkDFAToBuchi(dcDkAut);
        NBA dcBuchi = NBAOperations.fromDkNBA(dcDkAutAsBuchi, alphabet);
        options.stats.hypothesisMLDollar = dcBuchi;
       
        Automaton ba = UtilNBAMLDollar.dkDFAToBuchi(dkAut); 
        hypothesis = NBAOperations.fromDkNBA(ba, alphabet);
        options.stats.hypothesis = hypothesis;

    }

    private Automaton dollarComplement(Automaton input) {
        Automaton allUpWords = UtilNBAMLDollar.getAllUPWords(alphabet, dollarLetter);
        return BasicOperations.minus(allUpWords, input);
    }

    @Override
    public void refineHypothesis(Query<HashableValue> query) {
        Word prefix = query.getPrefix();
        Word suffix = query.getSuffix();
        options.log.println("Analyzing counterexample for DFA learner...");
        Automaton result = FDFAOperations.buildDDollar(prefix, suffix);
        // System.out.println(result.toString());
        String counterexample = null;
        DFA dfa = dfaLearner.getHypothesis();
        Automaton dkAut = DFAOperations.toDkDFA(dfa);
        //System.out.println(dkAut.toString());
        HashableValue answer = query.getQueryAnswer();
        if(answer == null) {
            answer = membershipOracle.answerMembershipQuery(query);
        }
        if (answer.isAccepting()) {
            counterexample = result.minus(dkAut).getShortestExample(true);
        } else {
            counterexample = dkAut.intersection(result).getShortestExample(true);
        }
        options.log.verbose("counterexample: " + counterexample);
        Word word = alphabet.getWordFromString(counterexample);
        Query<HashableValue> ceQuery = new QuerySimple<>(word, alphabet.getEmptyWord());
        ceQuery.answerQuery(answer);
        dfaLearner.refineHypothesis(ceQuery);
        constructHypothesis();
    }
    
    @Override
    public String toString() {
        return dfaLearner.toString();
    }
    
    public LearnerDFA getLearnerDFA() {
        return dfaLearner;
    }

    @Override
    public String toHTML() {
        return dfaLearner.toHTML();
    }
    
}
