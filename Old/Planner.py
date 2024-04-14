
from pddl import parse_domain, parse_problem

domain = parse_domain(".\Problems\Groupe3\maze_jumper.pddl")
problem = parse_problem('.\Problems\Groupe3\problems\maze_p0.pddl')

class OurGraphPlan():
    
    def __init__(self, domain, problem):
        self.actions = domain.actions
        self.predicates = domain.predicates
        self.goal = problem.goal
        self.init = problem.init
        self.objects = problem.objects
        
    def forward(self):
        pass
    
    def backward(self):
        pass
    
    def heuristic(self):
        pass