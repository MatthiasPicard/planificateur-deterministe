import random
import pddlpy
import pddl

# Termes utilisés (en se basant sur le cours)
# Literal (proposition)
# Action
# State : ensemble de littéraux
# Action_set : ensemble d'actions
# Level : niveau dans notre graphe (layer - couche)

# Logiquement, en suivant la construction d'un graphe dans le cours, on a toujours un state de plus qu'un action_set

# Notre state a une partie pos et une partie neg
class State:
	def __init__(self, pos: set, neg: set):
		self.pos = pos
		self.neg = neg

	def __str__(self):
		return f"pos : {self.pos}\nneg : {self.neg}"

	def copy(self):
		return State(self.pos.copy(), self.neg.copy())

# Pour définir une action (et non pas un action_set, qui est un ensemble d'actions !)
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
    
    def __eq__(self, other):
        return self.pre_pos == other.pre_pos and self.pre_neg == other.pre_neg and self.eff_pos == other.eff_pos and self.eff_neg == other.eff_neg

class GraphPlan:
    def __init__(self, domain_file, problem_file):
        self.dp = pddlpy.DomainProblem(domain_file,problem_file)
        init, goal = self.get_init(problem_file)
        self.state_levels = [init] # always longer than actions_levels
        self.action_set_levels = []
        self.goal = goal
        self.literal_mutexes = [[]] # list of list of pairs of mutex propositions (a propostion mutex is of the form ((prop1,is_true),(prop2,is_true)), to keep track of the negations)
        self.action_mutexes = [[]] # list of list of tuple of mutex actions

        '''
        Schéma pour les ensembles de mutex

        literal_mutexes
        [
            [(l1, l2)], # pour le level 1
            [(l1, l3)], # pour le level 2
            [(l2, l3)]
        ]

        [
            [(), (), ()]
        ]

        action_mutexes
        [
            [(a1, a3)],
            [(a4, a5), (a3, a5)]
        ]
        '''

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

    def forward(self, actions, state): # pour le backward faut garder une trace de quelles actions ont faites 
        next_action = set()
        effect_pos = set()
        effect_neg = set()
        for action in actions:
            if self.is_applicable(action, state):
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

    def create_next_layer(self):
        next_state = State(set(), set())
        next_action_set = set()
        for op in self.dp.operators():
            n_s, n_a = self.forward(self.dp.ground_operator(op), self.state_levels[-1])
            next_state.pos.update(n_s.pos)
            next_state.neg.update(n_s.neg)
            next_action_set.update(n_a)
        self.action_set_levels.append(next_action_set)
        self.state_levels.append(next_state)
        self.create_mutexes()
    
    def mutex_action(self, action1, action2):
        self.action_mutexes[-1].append((action1, action2))

    def mutex_literal(self, literal1, literal2, literal1_truth, literal2_truth):
        self.literal_mutexes[-1].append(((literal1, literal1_truth), (literal2, literal2_truth)))

    '''
    def is_mutex_action(self,action1, action2,action_index):
        set_actions = set([action1, action2])
        return set_actions in [set(elem) for elem in self.action_mutexes[action_index]]
    
    def is_mutex_prop(self,prop1, prop2,prop_index):
        set_props = set([prop1, prop2])
        return set_props in [set(elem) for elem in self.prop_mutexes[prop_index]]
    '''
    # Besoins concurrents : une précondition d’une action est mutex avec une précondition de l’autre

    # on regarde les préconditions d'une action
    # on regarde si elle est présente dans un mutex
    # on regarde si le littéral associé est dans les préconditions de l'autre action

    def is_mutex_actions(self, action1, action2):                    
        for t in self.literal_mutexes[-2]:
            if t[0][0] in action1.pre_pos and t[0][1] == True:
                if t[1][0] in action2.pre_pos and t[1][1] == True:
                    return True
                if t[1][0] in action2.pre_neg and t[1][1] == False:
                    return True
            if t[0][0] in action1.pre_neg and t[0][1] == False:
                if t[1][0] in action2.pre_pos and t[1][1] == True:
                    return True
                if t[1][0] in action2.pre_neg and t[1][1] == False:
                    return True
            if t[0][0] in action2.pre_pos and t[0][1] == True:
                if t[1][0] in action1.pre_pos and t[1][1] == True:
                    return True
                if t[1][0] in action1.pre_neg and t[1][1] == False:
                    return True
            if t[0][0] in action2.pre_neg and t[0][1] == False:
                if t[1][0] in action1.pre_pos and t[1][1] == True:
                    return True
                if t[1][0] in action1.pre_neg and t[1][1] == False:
                    return True
            if t[1][0] in action1.pre_pos and t[1][1] == True:
                if t[0][0] in action2.pre_pos and t[1][1] == True:
                    return True
                if t[0][0] in action2.pre_neg and t[1][1] == False:
                    return True
            if t[1][0] in action1.pre_neg and t[1][1] == False:
                if t[0][0] in action2.pre_pos and t[1][1] == True:
                    return True
                if t[0][0] in action2.pre_neg and t[1][1] == False:
                    return True
            if t[1][0] in action2.pre_pos and t[1][1] == True:
                if t[0][0] in action1.pre_pos and t[1][1] == True:
                    return True
                if t[0][0] in action1.pre_neg and t[1][1] == False:
                    return True
            if t[1][0] in action2.pre_neg and t[1][1] == False:
                if t[0][0] in action1.pre_pos and t[1][1] == True:
                    return True
                if t[0][0] in action1.pre_neg and t[1][1] == False:
                    return True
        return False

    def create_mutexes(self):
        action_set = self.action_set_levels[-1]
        state = self.state_levels[-1]
        previous_state = self.state_levels[-2]

        # Mutex actions
            # Effet inconsistent : un effet d’une action est la négation d’un effet de l’autre
            # Interférence : un effet d’une action est la négation d’une précondition de l’autre
            # Besoins concurrents : une précondition d’une action est mutex avec une précondition de l’autre

        # Mutex actions
            # Effet inconsistent : un effet d’une action est la négation d’un effet de l’autre

        for action1 in action_set:
            for action2 in action_set:
                if action1 != action2:
                    if not action1.eff_pos.isdisjoint(action2.eff_neg):
                        self.mutex_action(action1, action2)
                    if not action2.eff_pos.isdisjoint(action1.eff_neg):
                        self.mutex_action(action1, action2)

            # Interférence : un effet d’une action est la négation d’une précondition de l’autre
        for action1 in action_set:
            for action2 in action_set:
                if action1 != action2:
                    if not action1.eff_pos.isdisjoint(action2.pre_neg):
                        self.mutex_action(action1, action2)
                    if not action1.eff_neg.isdisjoint(action2.pre_pos):
                        self.mutex_action(action1, action2)
                    if not action2.eff_pos.isdisjoint(action1.pre_neg):
                        self.mutex_action(action1, action2)
                    if not action2.eff_neg.isdisjoint(action1.pre_pos):
                        self.mutex_action(action1, action2)

            # Besoins concurrents : une précondition d’une action est mutex avec une précondition de l’autre
        for action1 in action_set:
            for action2 in action_set:
                if action1 != action2:
                    if self.is_mutex_actions(action1.pre_pos, action2.pre_pos):
                        self.mutex_action(action1, action2)
                    if self.is_mutex_actions(action1.pre_pos, action2.pre_neg):
                        self.mutex_action(action1, action2)
                    if self.is_mutex_actions(action1.pre_neg, action2.pre_pos):
                        self.mutex_action(action1, action2)
                    if self.is_mutex_actions(action1.pre_neg, action2.pre_neg):
                        self.mutex_action(action1, action2)

        # Mutex littéraux
            # l’un est la négation de l’autre
            # toute paire possible d’actions pouvant accomplir ces 2 littéraux est mutex -> se sert des actions précédentes

        # Mutex littéraux
            # l’un est la négation de l’autre
        for literal in state.pos & state.neg: # le littéral est dans le pos et le neg # attention crée un set donc le for n'est pas possible
            self.mutex_literal(literal, literal, True, False)

            # toute paire possible d’actions pouvant accomplir ces 2 littéraux est mutex -> se sert des actions précédentes
        for literal in state.pos and state.neg:
            get_action_giving(literal)

        if is_mutex(get_action_giving(literal1), get_action_giving(literal2)):
            self.mutex_literal(literal, literal)

    def plan(self, current_level=None, goal=None):
        if current_level is None:
            current_level = len(self.state_levels) - 1
        if goal is None:
            goal = self.goal
        # Vérifier si le but est atteint dans le dernier état
        current_state = self.state_levels[current_level]
        if not (goal.pos <= current_state.pos and goal.neg <= current_state.neg):
            self.create_next_layer()
            return None  # Le plan n'est pas encore complet
        plan = []
        state_path = [current_state]
        action_path = []
        # Tant que nous ne sommes pas revenus à l'état initial
        while current_level > 0:
            current_actions = self.action_set_levels[current_level]
            no_mutex_actions = set()
            # Évaluer les mutex entre actions
            for action in current_actions:
                if not any(self.is_mutex_actions(action, other_action) for other_action in current_actions if action != other_action):
                    no_mutex_actions.add(action)
            if not no_mutex_actions:
                self.create_next_layer()
                return None

            # Vérifier les mutex de littéraux dans l'état actuel
            mutex_found = False
            for lit1 in current_state.pos:
                for lit2 in current_state.neg:
                    if self.mutex_literal(lit1, lit2, True, False):  # Suppose que cette méthode vérifie les mutex et retourne un booléen
                        mutex_found = True
                        break
                if mutex_found:
                    break

            if mutex_found:
                self.create_next_layer()
                return None

            action_path.append(no_mutex_actions)
            current_level -= 1
            current_state = self.state_levels[current_level]
            state_path.append(current_state)

        # Construire le plan en remontant
        plan = list(zip(reversed(state_path), reversed(action_path)))
        return plan 

    def graphplan(self,domain_file, problem_file):
        """Fonction qui englobe tout pour exécuter notre algorithme de graphplan"""
        
        stabilized = False
        while not stabilized:

            solution = self.plan(level, goal, actions, mutexes)
            if solution is not None:
                return solution
            
            self.create_next_layer()
            if self.prop_layers[-1] == self.prop_layers[-2]:
                stabilized = True
                
        return None
    
    def get_init(self,problem_file):
        init_neg_predicates = []
        init_pos_predicates = []
        problem = pddl.parse_problem(problem_file) # we need to use pddl to extract negations
        for predicate in list(problem.init):
            if isinstance(predicate, pddl.logic.base.Not):
                init_neg_predicates.append(tuple([str(predicate.argument.name)] + [str(c.name) for c in predicate.argument.terms]))
            elif isinstance(predicate, pddl.logic.predicates.Predicate) :
                init_pos_predicates.append(tuple([str(predicate.name)] + [str(c.name) for c in predicate.terms]))
            else:
                raise ValueError("Unknown predicate type")
        
        goal_neg_predicates = []
        goal_pos_predicates = [] 
        
        if isinstance(problem.goal,pddl.logic.predicates.Predicate):
            goal_pos_predicates.append(tuple([str(problem.goal.name)] + [str(c.name) for c in problem.goal.terms]))
        elif isinstance(problem.goal, pddl.logic.base.Not) :
            goal_neg_predicates.append(tuple([str(problem.goal.argument.name)] + [str(c.name) for c in predicate.argument.terms]))

        else:  
            for predicate in list(problem.goal.operands):
                if isinstance(predicate, pddl.logic.base.Not):
                    goal_neg_predicates.append(tuple([str(predicate.argument.name)] + [str(c.name) for c in predicate.argument.terms]))
                elif isinstance(predicate, pddl.logic.predicates.Predicate) :
                    goal_pos_predicates.append(tuple([str(predicate.name)] + [str(c.name) for c in predicate.terms]))
                else:
                    raise ValueError("Unknown predicate type")

        return State(set_str(init_pos_predicates), set_str(init_neg_predicates)), State(set_str(goal_pos_predicates), set_str(goal_neg_predicates))

def set_str(s: set):
    s_str = set()
    for i in s:
        s_str.add(str(i))
    return s_str  

if __name__ == "__main__":
    
    domain_file = ".\Problems\Groupe3\maze.pddl"
    problem_file = '.\Problems\Groupe3\problems\maze_p0.pddl'
    
    graph_plan_object = GraphPlan(domain_file, problem_file)
    plan = graph_plan_object.graphplan(domain_file, problem_file)
    
    if plan is None:
        print("No plan found.")
    else:
        print(plan)