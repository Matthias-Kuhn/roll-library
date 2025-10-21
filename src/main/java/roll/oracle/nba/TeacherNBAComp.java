package roll.oracle.nba;

import java.util.List;

import automata.FiniteAutomaton;
import dk.brics.automaton.Automaton;
import oracle.IntersectionCheck;
import roll.automata.NBA;
import roll.automata.operations.FDFAOperations;
import roll.automata.operations.NBAOperations;
import roll.learner.nba.ldollar.UtilNBALDollar;
import roll.main.Options;
import roll.main.complement.IsIncluded;
import roll.main.complement.UtilComplement;
import roll.main.inclusion.UtilInclusion;
import roll.oracle.nba.sampler.NBAInclusionSampler;
import roll.oracle.nba.sampler.SamplerIndexedMonteCarlo;
import roll.query.Query;
import roll.query.QuerySimple;
import roll.table.HashableValue;
import roll.table.HashableValueBoolean;
import roll.table.HashableValueBooleanExactPair;
import roll.util.Pair;
import roll.util.Timer;
import roll.words.Alphabet;
import roll.words.Word;

public class TeacherNBAComp extends TeacherNBA {

    Alphabet alphabet;
    public boolean sampling;

    public TeacherNBAComp(Options options, NBA target) {
        super(options, target);
        alphabet = target.getAlphabet();
    }

    @Override
    protected HashableValue checkMembership(Query<HashableValue> query) {
        Word prefix = query.getPrefix();
        Word suffix = query.getSuffix();
        boolean answer = NBAOperations.accepts(target, prefix, suffix);

        // flip answer for complement 
        answer = !answer;
        return new HashableValueBoolean(answer);
    }

    @Override
    protected Query<HashableValue> checkEquivalence(NBA hypothesis) {
        Timer timer = new Timer();
        timer.start();

        options.log.println("Checking the intersection of hypothesis (" + hypothesis.getStateSize() + ") and target ("+ target.getStateSize() + ")...");
        long t = timer.getCurrentTime();
        FiniteAutomaton rhyp = UtilInclusion.toRABITNBA(hypothesis);
        FiniteAutomaton rtar = UtilInclusion.toRABITNBA(target);
        IntersectionCheck checker = new IntersectionCheck(rhyp, rtar);

        boolean isEmpty = checker.checkEmptiness();
        t = timer.getCurrentTime() - t;

        if(options.verbose()) {
            options.log.println("Hypothesis for complementation B");
            options.log.println(hypothesis.toString());
        }
        Word prefix = null;
        Word suffix = null;
        boolean isEq = false, isInTarget = false;
        if(! isEmpty) {
            checker.computePath();
            Pair<Word, Word> pair = getCounterexample(checker.getPrefix(), checker.getSuffix());
            prefix = pair.getLeft();
            suffix = pair.getRight();
            isEq = false;
            isInTarget = true;
        } else {
            Automaton ldollarComp = options.stats.ldollarHypo.clone();
            Automaton dcBA = UtilNBALDollar.dkDFAToBuchi(ldollarComp);
            NBA dollarCompHypo = NBAOperations.fromDkNBA(dcBA, alphabet);
            //NBA dollarCompHypo = options.stats.dollarCompHypothesis;
            options.log.println("Checking the intersection for B(F) (" + target.getStateSize() + ") and B(F^c) ("
                    + dollarCompHypo.getStateSize() + ")...");
    
            t = timer.getCurrentTime();
            FiniteAutomaton rdch = UtilInclusion.toRABITNBA(dollarCompHypo);
            checker = new IntersectionCheck(rdch, rtar);
            isEmpty = checker.checkEmptiness();
            t = timer.getCurrentTime() - t;

            if (false) {
                // we have found counterexample now
                checker.computePath();
                Pair<Word, Word> pair = getCounterexample(checker.getPrefix(), checker.getSuffix());
                prefix = pair.getLeft();
                suffix = pair.getRight();
                isEq = false;
                isInTarget = NBAOperations.accepts(target, prefix, suffix);
            } else {
                
                boolean hasCE = false;
                
                /**
                 * the counterexamples returned from the sampler are nondeterministic,
                 * we do not encourage nondeterminism in the tool 
                 * **/
                boolean nondet = false;
                if(nondet && sampling) {
                    options.log.println("Sampling for a counterexample to the inclusion...");
                    SamplerIndexedMonteCarlo sampler = new SamplerIndexedMonteCarlo(options.epsilon, options.delta);
                    sampler.K = target.getStateSize();
                    Query<HashableValue> ceQuery = NBAInclusionSampler.isIncluded(dollarCompHypo, target, sampler);
                    if (ceQuery != null) {
                        prefix = ceQuery.getPrefix();
                        suffix = ceQuery.getSuffix();
                        isInTarget = false;
                        isEq = false;
                        hasCE = true;
                    }
                }
//            	UtilComplement.print(BFC, "A.ba");
//            	UtilComplement.print(B, "B.ba");
                if(! hasCE) {
                    // by rabit
                    options.log.println("RABIT/SPOT/CONGR for a counterexample to the inclusion...");
                    t = timer.getCurrentTime();
					IsIncluded included = UtilComplement.checkInclusion(options, alphabet, dollarCompHypo, target, rdch, rtar);                
                    t = timer.getCurrentTime() - t;
                    
                    boolean isIncluded = included.isIncluded();
                    if (isIncluded) {
//                    	UtilComplement.print(BFC, "A.ba");
//                    	UtilComplement.print(B, "B.ba");
                        isEq = true;
                    } else {
                        isInTarget = false;
                        // check whether it is in A
                        prefix = included.getCounterexample().getLeft();
                        suffix = included.getCounterexample().getRight();
                        isEq = false;
                        if(prefix == null || suffix == null) {
                        	throw new RuntimeException("Reported not included yet no counterexample has been returned");
                        }
                    }
                }
            }
        }
        
        options.log.println("Done for checking equivalence...");
        Query<HashableValue> query = null;
    

        if (isEq) {
            Word empty = alphabet.getEmptyWord();
            query = new QuerySimple<>(empty, empty);
            query.answerQuery(new HashableValueBoolean(true));
        } else {
            query = new QuerySimple<>(prefix, suffix);
            query.answerQuery(new HashableValueBoolean(false));
        }
        
        timer.stop();
        options.stats.timeOfEquivalenceQuery += timer.getTimeElapsed();
        ++ options.stats.numOfEquivalenceQuery;
        options.stats.timeOfLastEquivalenceQuery = timer.getTimeElapsed();
        
        if(options.verbose()) options.log.println("counter example = " + query);
        return query;
    }

    private Pair<Word, Word> getCounterexample(List<String> prefix, List<String> suffix) {
        return UtilComplement.getCounterexample(alphabet, prefix, suffix);
    }
    
}
