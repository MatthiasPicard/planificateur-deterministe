import sys
import time
from util import Pair
from propositionLayer import PropositionLayer
from planGraphLevel import PlanGraphLevel
from pddl import parse_domain, parse_problem
from action import Action

class GraphPlan(object):
    """
    Initializes and runs the GraphPlan algorithm.
    """

    def __init__(self, domain, problem):
        self.independentActions = []
        self.noGoods = []
        self.graph = []
        domain = parse_domain(domain)
        problem = parse_problem(problem)
        self.actions = domain.actions
        self.predicates = domain.predicates
        self.goal = problem.goal
        self.initialState = problem.init
        self.objects = problem.objects
        self.propositions = self.extractPropositions(self.initialState, self.actions)
        self.createNoOps()
        self.independent()
        PlanGraphLevel.setIndependentActions(self.independentActions)
        PlanGraphLevel.setActions(self.actions)
        PlanGraphLevel.setProps(self.propositions)

    def extractPropositions(self, initialState, actions):
        """
        Extracts unique propositions from initial states and action effects.
        """
        propositions = set(initialState)
        for action in actions:
            propositions.update(action.add + action.precond + action.delete)
        return list(propositions)

    def createNoOps(self):
        """
        Creates NoOp actions that are used to propagate propositions from one layer to the next.
        """
        for prop in self.propositions:
            act = Action(prop.name, [prop], [prop], [], True)
            self.actions.append(act)
            prop.addProducer(act)

    def independent(self):
        """
        Determines which actions are independent of each other.
        """
        for act1 in self.actions:
            for act2 in self.actions:
                if independentPair(act1, act2):
                    self.independentActions.append(Pair(act1, act2))

    def graphPlan(self):
        initState = self.initialState
        level = 0
        self.noGoods = [[]]
        propLayerInit = PropositionLayer()
        for prop in initState:
            propLayerInit.addProposition(prop)
        pgInit = PlanGraphLevel()
        pgInit.setPropositionLayer(propLayerInit)
        self.graph.append(pgInit)

        while self.goalStateNotInPropLayer(self.graph[level].getPropositionLayer().getPropositions()) or \
              self.goalStateHasMutex(self.graph[level].getPropositionLayer()):
            if self.isFixed(level):
                return None
            self.noGoods.append([])
            level += 1
            pgNext = PlanGraphLevel()
            pgNext.expand(self.graph[level - 1])
            self.graph.append(pgNext)

        plan = self.extract(self.graph, self.goal, level)
        while plan is None:
            level += 1
            self.noGoods.append([])
            pgNext = PlanGraphLevel()
            pgNext.expand(self.graph[level - 1])
            self.graph.append(pgNext)
            plan = self.extract(self.graph, self.goal, level)
            if plan is None and self.isFixed(level):
                if len(self.noGoods[level]) == len(self.noGoods[level - 1]):
                    return None
        return plan

def independentPair(a1, a2):
    if a1 == a2:
        return True
    a1a, a2a = set(a1.getAdd()), set(a2.getAdd())
    a1d, a2d = set(a1.getDelete()), set(a2.getDelete())
    a1p, a2p = set(a1.getPre()), set(a2.getPre())

    if (a1a & a2d) or (a2a & a1d) or (a1p & a2d) or (a2p & a1d):
        return False
    return True

if __name__ == '__main__':
    domain = ".\\Problems\\Groupe3\\maze_jumper.pddl"
    problem = '.\\Problems\\Groupe3\\problems\\maze_p0.pddl'
    if len(sys.argv) == 3:
        domain, problem = sys.argv[1], sys.argv[2]
    gp = GraphPlan(domain, problem)
    start = time.time()
    plan = gp.graphPlan()
    elapsed = time.time() - start
    if plan:
        print(f"Plan found with {len([act for act in plan if not act.isNoOp()])} actions in {elapsed:.2f} seconds")
    else:
        print(f"Could not find a plan in {elapsed:.2f} seconds")
