import pddlpy
import pddl

# Notre state a une partie pos et une partie neg
class State:
	def __init__(self, pos: set, neg: set):
		self.pos = pos
		self.neg = neg

	def __str__(self):
		return f"pos : {self.pos}\nneg : {self.neg}"

	def copy(self):
		return State(self.pos.copy(), self.neg.copy())


class Action:
    def __init__(self, pre_pos, pre_neg, eff_pos, eff_neg):
        self.pre_pos = pre_pos
        self.pre_neg = pre_neg
        self.eff_pos = eff_pos
        self.eff_neg = eff_neg

    def __str__(self):
        return f"pre_pos : {self.pre_pos}\npre_neg : {self.pre_neg}\neff_pos : {self.eff_pos}\neff_neg : {self.eff_neg}\n"

    def __repr__(self):
        return f"pre_pos : {self.pre_pos}\npre_neg : {self.pre_neg}\neff_pos : {self.eff_pos}\neff_neg : {self.eff_neg}\n"
    
class GraphPlan:
    
    def __init__(self,domain_file, problem_file):
        self.action_layers = []
        self.prop_layers = [get_init_state(problem_file)] # always longer than actions_layers
        self.dp = pddlpy.DomainProblem(domain_file,problem_file)
        self.prop_mutexes = [[]]   # list of list of pairs of mutex actions
        self.action_mutexes = [[]] # list of list of pairs of mutex actions
        
          
    def create_next_layer(self):
        next_state = State(set(), set())
        next_action = set()
        for op in self.dp.operators():
            n_s, n_a = self.forward(self.dp.ground_operator(op), self.prop_layers[-1])
            next_state.pos.update(n_s.pos)
            next_state.neg.update(n_s.neg)
            next_action.update(n_a)
        self.action_layers.append(next_action)
        self.prop_layers.append(next_state)
        self.create_mutexes(next_state,next_action
                            ,len(self.prop_layers),len(self.action_layers) # layer_indexes
                            )

    def forward(self,actions, state):# pour le backward faut garder une trace de quelles actions ont faites 
        next_action = set()
        effect_pos = set()
        effect_neg = set()
        for action in actions:
            if is_applicable(action, state):
                p_pos = set_str(action.precondition_pos)
                p_neg = set_str(action.precondition_neg)
                e_pos = set_str(action.effect_pos)
                e_neg = set_str(action.effect_neg)
                next_action.add(Action(p_pos, p_neg, e_pos, e_neg))
                effect_pos.update(e_pos)
                effect_neg.update(e_neg)
        next_state = state.copy()
        next_state.pos.update(effect_pos)
        next_state.neg.update(effect_neg)
        return next_state, next_action
    
    def create_mutexes(self,prop_layer,prop_action,layer_index,action_index):
        for i in prop_layer.pos: # if i is in j.pos or j.neg, then i and j are mutexes
            for j in prop_layer.neg:
                if i == j:
                    self.prop_mutexes[layer_index].append((i,j))

    def plan(self):
        current_state = State(self.initial_state_pos, self.initial_state_neg)
        goal_state_set = self.goal_state 
        plan = []
        print(current_state.neg)
        
        while current_state.pos != goal_state_set:
            applicable_actions = [
                action for action in self.actions 
                if action.is_applicable(current_state.pos, current_state.neg)
            ]
            if not applicable_actions:
                print("No applicable actions to reach the goal state.")
                return None

            # Sélection de l'action avec le plus grand nombre d'effets positifs partagés avec l'état but
            best_action = max(applicable_actions, key=lambda x: len(set(x.eff_pos) & goal_state_set))
            plan.append(best_action)
            print(best_action)
            print(current_state.pos, current_state.neg)

            # Mise à jour de l'état courant après application de la meilleure action
            current_state = best_action.apply(current_state)

        return plan
        
                  
def set_str(s: set):
    s_str = set()
    for i in s:
        s_str.add(str(i))
    return s_str


def is_applicable(action, state):
    a_pos = set_str(action.precondition_pos)
    a_neg = set_str(action.precondition_neg)
    if not a_pos <= state.pos:
        return False
    if a_neg <= state.neg:
        return True
    else:
        if (a_neg - state.neg).isdisjoint(state.pos):
            state.neg.update(a_neg) # On choisit d'update le state plutôt que le next_state, la maj effectuée est sur des prédicats déjà présents (puisque hypothèse du monde clos)
            return True
        else:
            return False
        
def get_init_state(problem_file):
    neg_predicates = []
    pos_predicates = []
    problem = pddl.parse_problem(problem_file) # we need to use pddl to extract negations
    for predicate in list(problem.init):
        if isinstance(predicate, pddl.logic.base.Not):
            neg_predicates.append(tuple([str(predicate.argument.name)] + [str(c.name) for c in predicate.argument.terms]))
        elif isinstance(predicate, pddl.logic.predicates.Predicate) :
            pos_predicates.append(tuple([str(predicate.name)] + [str(c.name) for c in predicate.terms]))
        else:
            raise ValueError("Unknown predicate type")

    return State(set_str(pos_predicates), set_str(neg_predicates)) 


def graphplan(domain_file, problem_file):
    """Fonction qui englobe tout pour exécuter notre algorithme de graphplan"""
    
    domprob = get_init_state(domain_file, problem_file)

    init = domprob.initialstate()
    goal = domprob.goals()
    actions = domprob.operators()

    # Initialize the level to 0
    level = {0: init}

    # Initialize a dictionary to store the mutex relations
    mutexes = defaultdict(set)

    # Graphplan algorithm
    while True:
        # Try to find a solution
        solution = search_for_solution(level, goal, actions, mutexes)
        if solution is not None:
            return solution

        # Expand the graph by adding a new level
        level = expand_graph(level, actions, mutexes)


if __name__ == "__main__":
    domain = ".\Problems\Groupe3\maze.pddl"
    problem = '.\Problems\Groupe3\problems\maze_p0.pddl'
    graphplan(domain_file, problem_file)