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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import dk.brics.automaton.Automaton;
import dk.brics.automaton.BasicOperations;
import dk.brics.automaton.Transition;
import roll.automata.DFA;
import roll.automata.NBA;
import roll.automata.operations.DFAOperations;
import roll.automata.operations.FDFAOperations;
import roll.automata.operations.NBAIntersectionCheck;
import roll.automata.operations.NBAOperations;
import roll.learner.LearnerBase;
import roll.learner.LearnerDFA;
import roll.learner.LearnerType;
import roll.learner.dfa.table.LearnerMDFATableColumn;
import roll.learner.dfa.tree.LearnerDFATreeColumn;
import roll.learner.nba.ldollar.UtilNBALDollar;
import roll.main.Options;
import roll.oracle.MembershipOracle;
import roll.parser.Format;
import roll.parser.Parser;
import roll.parser.UtilParser;
import roll.query.Query;
import roll.query.QuerySimple;
import roll.table.HashableValue;
import roll.words.Alphabet;
import roll.words.Word;
import dk.brics.automaton.State;

/**
 * @author Yong Li (liyong@ios.ac.cn)
 * 
 * This class implements the BA learning algorithm from the paper 
 * Azadeh Farzan, Yu-Fang Chen, Edmund M. Clarke, Yih-Kuen Tsay and Bow-Yaw Wang
 *       "Extending automated compositional verification to the full class of omega-regular languages"
 * in TACAS 2008
 * */

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
                Word word = alphabet.getWordFromString(counterexample);
                Query<HashableValue> ceQuery = new QuerySimple<>(word, alphabet.getEmptyWord());
                ceQuery.answerQuery(getHashableValueBoolean(false));
                dfaLearner.refineHypothesis(ceQuery);
            }else {
                // DFA accepts a subset of E*$E+
                //DFA testSaturation = dfaLearner.getHypothesis();
                //Automaton satDk = DFAOperations.toDkDFA(testSaturation);
//
                //Automaton dcSatDk = dollarComplement(satDk);
//
                //Automaton satAsBuchi = UtilNBAMLDollar.dkDFAToBuchi(satDk);
                //Automaton dcSatAsBuchi = UtilNBAMLDollar.dkDFAToBuchi(dcSatDk);
//
                //Automaton satInter = satAsBuchi.intersection(dcSatAsBuchi);
                //String satCounterExample = satInter.getShortestExample(true);
                //if (satCounterExample != null) {
                //    Word word = alphabet.getWordFromString(satCounterExample);
                //    Query<HashableValue> ceQuery = new QuerySimple<>(word, alphabet.getEmptyWord());
                //    ceQuery.answerQuery(getHashableValueBoolean(false));
                //    dfaLearner.refineHypothesis(ceQuery);
                //} else {
                //    break;
                //}
                break;

                
            }
        }
        // now we construct the NBA

        DFA dfa1 = dfaLearner.getHypothesis();
        Automaton dkAut1 = DFAOperations.toDkDFA(dfa1);

        Parser parser = UtilParser.prepare(options, options.inputFile, Format.BA);
        //System.out.println(dkAut1.toString());

        Automaton mkComplement = mkComplement(dkAut1);
        Automaton allUpWords = UtilNBAMLDollar.getAllUPWords(alphabet, dollarLetter);
        Automaton intersection = mkComplement.intersection(allUpWords);
        //intersection.determinize();
        Automaton intAsBuchi = UtilNBAMLDollar.dkDFAToBuchi(intersection);
        
        Automaton mkMinus = BasicOperations.minus(allUpWords, dkAut);
        NBA buchi = NBAOperations.fromDkNBA(intAsBuchi, alphabet);

        Automaton mkAsBuchi = UtilNBAMLDollar.dkDFAToBuchi(mkMinus);
        NBA mknbabuchi = NBAOperations.fromDkNBA(mkAsBuchi, alphabet);


        //System.out.println(intAsBuchi.toDot());
        //System.out.println("MK Minus");
        //System.out.println(BasicOperations.minus(allUpWords, dkAut));
        //System.out.println("dkAut");
        //System.out.println(dkAut); 
        //System.out.println(dkAut.toDot()); 
        //
        //System.out.println(mkComplement.toDot()); 
        //System.out.println(buchi.toBA());
        System.out.println("----");   
        //System.out.println(mknbabuchi.toBA());   
        //System.out.println(dfaLearner.toString());   

        options.stats.hypothesisMLDollar = mknbabuchi;
        

        // test of double dollar-complementing the automaton
        Automaton comp = dollarComplement(dkAut);
        Automaton comp2 = dollarComplement(comp);

        Automaton copy = dkAut.clone();
        //removeSelfLoopsAtDollarStates(copy);
        //System.out.println(copy.toDot());
        //System.out.println(dkAut.toDot());

        Automaton ba = UtilNBAMLDollar.dkDFAToBuchi(dkAut); // instead of dkAut
        hypothesis = NBAOperations.fromDkNBA(ba, alphabet);
        options.stats.hypothesis = hypothesis;

        Automaton interAuto = ba.intersection(mkAsBuchi);
        String inBoth = interAuto.getShortestExample(true);
        if(inBoth != null) {
            System.out.println("Not correct");
            options.stats.mkMessage="Not correct";
        } else {
            System.out.println("Correct");
            options.stats.mkMessage = "Correct";
        }

        Automaton dollarComp = dollarComplement(dkAut);
        Automaton dollarCompNBA = UtilNBALDollar.dkDFAToBuchi(dollarComp);
        //NBA dcn = NBAOperations.fromDkNBA(dollarCompNBA, alphabet);
        //NBAIntersectionCheck checker = new NBAIntersectionCheck(hypothesis, dcn);
        //checker.computePath();

        //Automaton inter = ba.intersection(dollarCompNBA);

       // String ce = inter.getShortestExample(true);
        System.out.print("intersection");
        //System.out.println(checker.isEmpty());
        //if (ce != null) {
        //    System.out.println(ce);
        //    Word ceWord = alphabet.getWordFromString(ce);
        //    // Dieses Wort ist ein Gegenbeispiel zur Saturiertheit:
        //    Query<HashableValue> ceQuery = new QuerySimple<>(ceWord, alphabet.getEmptyWord());
        //    // Da es im Komplement ist, also nicht akzeptiert werden sollte:
        //    ceQuery.answerQuery(getHashableValueBoolean(false));
        //    dfaLearner.refineHypothesis(ceQuery);
        //    // Rekonstruiere neue Hypothese:
        //    constructHypothesis();
        //}

        //System.out.println("----");   
        //System.out.println("LDOLLAR");   
        //System.out.println(hypothesis.toBA());
    }

    public static Automaton removeSelfLoopsAtDollarStates(Automaton aut) {
        aut.determinize();
        Set<State> dollarStates = new HashSet<>();

        // 1. Finde Dollar-Zustände
        for (State s : aut.getStates()) {
            for (Transition t : s.getTransitions()) {
                if (t.getMin() == '$' && t.getMax() == '$') {
                    dollarStates.add(t.getDest());
                }
            }
        }

        // 2. Erzeuge Kopien für Selbstloops
        Map<State, State> copies = new HashMap<>();
        for (State q : dollarStates) {
            State copy = new State();
            if (q.isAccept()) copy.setAccept(true);
            copies.put(q, copy);
        }

        // 3. Übergänge anpassen
        for (State q : aut.getStates()) {
            Set<Transition> transitions = new HashSet<>(q.getTransitions());
            q.getTransitions().clear();

            for (Transition t : transitions) {
                if (dollarStates.contains(q) && t.getDest() == q) {
                    // war Selbstloop in Dollarzustand
                    State copy = copies.get(q);
                    q.addTransition(new Transition(t.getMin(), t.getMax(), copy));
                } else {
                    q.addTransition(t);
                }
            }
        }

        // 4. Übergänge für Kopien übernehmen
        for (Map.Entry<State, State> e : copies.entrySet()) {
            State orig = e.getKey();
            State copy = e.getValue();
            for (Transition t : orig.getTransitions()) {
                copy.addTransition(new Transition(t.getMin(), t.getMax(), t.getDest()));
            }
        }

        return aut;
    }

    private Automaton dollarComplement(Automaton input) {
        Automaton allUpWords = UtilNBAMLDollar.getAllUPWords(alphabet, dollarLetter);
        return BasicOperations.minus(allUpWords, input);
    }

    private Automaton mkComplement(Automaton input) {
        Automaton result = input.clone();
        for (dk.brics.automaton.State state: result.getStates()) {
            state.setAccept(!state.isAccept());
        }
        return result;
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
