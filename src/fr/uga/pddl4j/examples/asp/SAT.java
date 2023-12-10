package fr.uga.pddl4j.examples.asp;

import fr.uga.pddl4j.parser.DefaultParsedProblem;
import fr.uga.pddl4j.plan.Plan;
import fr.uga.pddl4j.plan.SequentialPlan;
import fr.uga.pddl4j.planners.AbstractPlanner;
import fr.uga.pddl4j.planners.statespace.HSP;
import fr.uga.pddl4j.problem.*;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.util.BitVector;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.sat4j.core.VecInt;
import org.sat4j.pb.SolverFactory;
import org.sat4j.specs.*;
import picocli.CommandLine;

import java.util.ArrayList;

import java.util.List;



@CommandLine.Command(name = "SAT",
        version = "ASP 1.0",
        description = "Solves a specified planning problem using A* search strategy.",
        sortOptions = false,
        mixinStandardHelpOptions = true,
        headerHeading = "Usage:%n",
        synopsisHeading = "%n",
        descriptionHeading = "%nDescription:%n%n",
        parameterListHeading = "%nParameters:%n",
        optionListHeading = "%nOptions:%n")


public class SAT extends AbstractPlanner {

    /**
     * The class logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(SAT.class.getName());
    /**
     * Instantiates the planning problem from a parsed problem.
     *
     * @param problem the problem to instantiate.
     * @return the instantiated planning problem or null if the problem cannot be instantiated.
     */
    @Override
    public Problem instantiate(DefaultParsedProblem problem) {
        final Problem pb = new DefaultProblem(problem);
        pb.instantiate();
        return pb;
    }

    /*
    * The function solves a planning problem by encoding it as a propositional satisfiability problem
    * and using a SAT solver to find a satisfying assignment.
    * 
    * @param problem The problem object contains information about the initial state, goal state,
    * fluents, actions, and constant symbols of the planning problem.
    * @return The method is currently returning null.
    */
    @Override
    public Plan solve(final Problem problem) {

        // initializing the initial state of the planning problem.
        Plan plan = new SequentialPlan();

        List<Fluent> pbFluents = problem.getFluents(); 
        int nbFluents = pbFluents.size();

        InitialState initialState = problem.getInitialState(); 
        BitVector initialStatePositiveFluents = initialState.getPositiveFluents(); 

        int[] initialStateFluentsSign = new int[nbFluents]; 
        for(int i=0; i<initialStateFluentsSign.length; i++){
            initialStateFluentsSign[i] = -(i+1); 
        }

        int[] initialPosFluents = initialStatePositiveFluents.stream().toArray(); 
        for(int i=0; i<initialPosFluents.length ;i++){
            initialStateFluentsSign[initialPosFluents[i]] = - initialStateFluentsSign[initialPosFluents[i]]; 
        }

        // retrieving the goal state from the planning problem and converting it
        // into a propositional satisfiability problem.
        Goal goalState = (Goal) problem.getGoal(); 

        BitVector goalStatePositiveFluents = goalState.getPositiveFluents();

        int[] goalStateFluentsSign = new int[nbFluents];

        for(int i=0; i<goalStateFluentsSign.length ;i++){ 
            goalStateFluentsSign[i] = -(i+1);
        }

        int[] goalPosFluents = goalStatePositiveFluents.stream().toArray();
        for(int i=0; i<goalPosFluents.length; i++){
            goalStateFluentsSign[goalPosFluents[i]] = -goalStateFluentsSign[goalPosFluents[i]]; 
        }

        // retrieving the list of actions from the planning problem and
        // initializing a 3-dimensional array called `vectorActions` to store the preconditions,
        // positive effects, and negative effects of each action.
        List<Action> problemActions = problem.getActions();
       
        int[][][] vectorActions = new int[problemActions.size()][3][]; 
        int[][] pivot = new int[3][]; 

        int numberOfAction = 0; 

        // iterating over the list of actions in the planning problem
        // (`problemActions`). For each action, it retrieves the positive fluents from the
        // precondition, positive effects, and negative effects.
        for(Action problemAction: problemActions){
            pivot[0] = problemAction.getPrecondition().getPositiveFluents().stream().toArray();
            pivot[1] = problemAction.getConditionalEffects().get(0).getEffect().getPositiveFluents().stream().toArray();
            pivot[2] = problemAction.getConditionalEffects().get(0).getEffect().getNegativeFluents().stream().toArray();

            for(int j =0; j<pivot[0].length;j++){
                pivot[0][j] = pivot[0][j]+1; 
            }
            for(int j =0; j<pivot[1].length;j++){
                pivot[1][j] = pivot[1][j]+1; 
            }

            for(int j =0; j<pivot[2].length;j++){
                pivot[2][j] = -(pivot[2][j]+1); 
            }

            vectorActions[numberOfAction][0] = pivot[0];
            vectorActions[numberOfAction][1] = pivot[1]; 
            vectorActions[numberOfAction][2] = pivot[2]; 

            numberOfAction++; 
        }

        // encoding the planning problem as a propositional satisfiability problem and using a SAT
        // solver to find a satisfying assignment.
        double n = 0;
        int D = problem.getConstantSymbols().size();
        int Ap = 0;
        for(Fluent flu : pbFluents ){
            if(Ap < flu.getArguments().length){
                Ap = flu.getArguments().length;
               
            }
        }

        final int maxVar = 1000000;
        final int nbClauses = numberOfAction;

        ISolver solver = SolverFactory.newDefault();

      
        try {
            solver.addClause(new VecInt(initialStateFluentsSign)); 
            solver.addClause(new VecInt(goalStateFluentsSign));
        } catch (ContradictionException e) {
            throw new RuntimeException(e);
        }

        List<Integer> clausePivot = new ArrayList<>(); 

        for (int i=0;i<nbClauses;i++) {
          
            for(int prec : vectorActions[i][0]){
                clausePivot.add(prec);
            }

     
            for(int pos : vectorActions[i][1]){
                clausePivot.add(-pos); 
            }

            for(int neg : vectorActions[i][2]){
                clausePivot.add(-neg); 
            }


            int[] deuxiemePivot = new int[clausePivot.size()];
            for(int j=0;j<clausePivot.size();j++){
                deuxiemePivot[j] = clausePivot.get(j);
            }

            try {
                solver.addClause(new VecInt(deuxiemePivot)); 
                        } catch (ContradictionException e) {
                throw new RuntimeException(e);
            }

            clausePivot.clear();
        }

        // check if the planning problem is satisfiable.
        try {
            if (solver.isSatisfiable()) {
                System.out.println("Satisfiable !");
                for(int num : solver.findModel()){
                    System.out.println(num);
                }

            } else {
                System.out.println("Unsatisfiable !");
            }
        } catch (TimeoutException e) {
            System.out.println("Timeout, sorry!");
        }

        return null;
    }

    /**
     * The main method of the <code>ASP</code> planner.
     *
     * @param args the arguments of the command line.
     */
    public static void main(String[] args) {
        try {
            final SAT satPlanner = new SAT(); 
            final HSP hspPlanner = new HSP(); 

            CommandLine cmd = new CommandLine(satPlanner);
            // CommandLine cmd = new CommandLine(hspPlanner);

            // cmd.execute("pddl/blocks_domain.pddl","pddl/blocks/p001.pddl");
            // cmd.execute("pddl/depots_domain.pddl","pddl/depots/p01.pddl");
            // cmd.execute("pddl/gripper_domain.pddl","pddl/gripper/p01.pddl");
            cmd.execute("pddl/logistics_domain.pddl","pddl/logistics/p01.pddl");

            // cmd.execute("pddl/blocks_domain.pddl","pddl/blocks/p002.pddl");
            // cmd.execute("pddl/depots_domain.pddl","pddl/depots/p02.pddl");
            // cmd.execute("pddl/gripper_domain.pddl","pddl/gripper/p02.pddl");
            cmd.execute("pddl/logistics_domain.pddl","pddl/logistics/p02.pddl");

            // cmd.execute("pddl/blocks_domain.pddl","pddl/blocks/p003.pddl");
            // cmd.execute("pddl/depots_domain.pddl","pddl/depots/p03.pddl");
            // cmd.execute("pddl/gripper_domain.pddl","pddl/gripper/p03.pddl");
            cmd.execute("pddl/logistics_domain.pddl","pddl/logistics/p03.pddl");
            
            // cmd.execute("pddl/blocks_domain.pddl","pddl/blocks/p004.pddl");
            // cmd.execute("pddl/depots_domain.pddl","pddl/depots/p04.pddl");
            // cmd.execute("pddl/gripper_domain.pddl","pddl/gripper/p04.pddl");
            cmd.execute("pddl/logistics_domain.pddl","pddl/logistics/p04.pddl");
            
        } catch (IllegalArgumentException e) {
            LOGGER.fatal(e.getMessage());
        }
    }
}

