import sys
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
    def __init__(self, name, pre_pos, pre_neg, eff_pos, eff_neg):
        self.name = name
        self.pre_pos = pre_pos
        self.pre_neg = pre_neg
        self.eff_pos = eff_pos
        self.eff_neg = eff_neg

    def __str__(self):
        return f"name : {self.name}\npre_pos : {self.pre_pos}\npre_neg : {self.pre_neg}\neff_pos : {self.eff_pos}\neff_neg : {self.eff_neg}\n"

    def __repr__(self):
        return f"name : {self.name}\npre_pos : {self.pre_pos}\npre_neg : {self.pre_neg}\neff_pos : {self.eff_pos}\neff_neg : {self.eff_neg}\n"
    
    def __eq__(self, other):
        return self.pre_pos == other.pre_pos and self.pre_neg == other.pre_neg and self.eff_pos == other.eff_pos and self.eff_neg == other.eff_neg
    
    def __hash__(self):
        return hash((self.name, self.pre_pos, self.pre_neg, self.eff_pos, self.eff_neg))

class GraphPlan:
    def __init__(self, domain_file, problem_file):
        self.dp = pddlpy.DomainProblem(domain_file,problem_file)
        init, goal = self.get_init(problem_file)
        self.state_levels = [init] # always longer than actions_levels
        self.action_set_levels = []
        self.goal = goal
        self.literal_mutexes = list() # list of list of pairs of mutex propositions (a propostion mutex is of the form ((prop1,is_true),(prop2,is_true)), to keep track of the negations)
        self.action_mutexes = list() # list of list of tuple of mutex actions

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

    def is_applicable(self, action, state):
        a_pos = set_str(action.precondition_pos)
        a_neg = set_str(action.precondition_neg)
        if not a_pos <= state.pos:
            return False
        if a_neg <= state.neg:
            return True
        else:
            if (a_neg - state.neg).isdisjoint(state.pos):
                state.neg.update(a_neg) # On choisit d'update le state plutôt que le next_state, la maj effectuée est sur des prédicats déjà présents (puisque hypothèse du monde clos)
                print(state.neg)
                return True
            else:
                return False

    def forward(self, actions, state, name_action): # pour le backward faut garder une trace de quelles actions ont faites 
        next_action = set()
        effect_pos = set()
        effect_neg = set()
        for action in actions:
            if self.is_applicable(action, state):
                print(state.neg)
                p_pos = set_str(action.precondition_pos)
                p_neg = set_str(action.precondition_neg)
                e_pos = set_str(action.effect_pos)
                e_neg = set_str(action.effect_neg)
                next_action.add(Action(name_action, frozenset(p_pos), frozenset(p_neg), frozenset(e_pos), frozenset(e_neg)))
                effect_pos.update(e_pos)
                effect_neg.update(e_neg)

        print(state.pos)
        print(state.neg)
        # Actions persistence
        for literal in state.pos:
            next_action.add(Action("Persitent_" + str(literal), frozenset({literal}), frozenset(), frozenset({literal}), frozenset()))
        for literal in state.neg:
            next_action.add(Action("Persitent_" + str(literal), frozenset(), frozenset({literal}), frozenset(), frozenset({literal})))

        print(next_action)

        next_state = state.copy()
        next_state.pos.update(effect_pos)
        next_state.neg.update(effect_neg)
        return next_state, next_action

    def create_next_layer(self):
        next_state = State(set(), set())
        next_action_set = set()
        for op in self.dp.operators():
            n_s, n_a = self.forward(self.dp.ground_operator(op), self.state_levels[-1], op)
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

    def is_mutex_action(self, action1, action2):                    
        for t in self.literal_mutexes[-1]:
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

    def is_mutex_literal(self, actions1, actions2):
        list_bool = []
        if actions1 == [] or actions2 == []:
            return False
        for action1 in actions1:
            for action2 in actions2:
                if not ((action1, action2) in self.action_mutexes[-1]):
                    #print((action1, action2))
                    return False
        return True

    def get_action(self, literal, index, truth):
        list_actions = list()
        for action in self.action_set_levels[index]: # la création des actions persistentes est anormale
            if truth:
                if literal in action.eff_pos:
                    list_actions.append(action)
            else:
                if literal in action.eff_neg:
                    list_actions.append(action)
        return list_actions

    def create_mutexes(self):
        self.literal_mutexes.append(list())
        self.action_mutexes.append(list())
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
                    if not action1.eff_neg.isdisjoint(action2.pre_pos):
                        self.mutex_action(action1, action2)
                    if not action2.eff_neg.isdisjoint(action1.pre_pos):
                        self.mutex_action(action1, action2)

            # Besoins concurrents : une précondition d’une action est mutex avec une précondition de l’autre
        for action1 in action_set:
            for action2 in action_set:
                if action1 != action2:
                    if self.is_mutex_action(action1, action2):
                        self.mutex_action(action1, action2)

        # Mutex littéraux
            # l’un est la négation de l’autre
            # toute paire possible d’actions pouvant accomplir ces 2 littéraux est mutex -> se sert des actions précédentes

        # Mutex littéraux
            # l’un est la négation de l’autre
        for literal in list(state.pos & state.neg):
            self.mutex_literal(literal, literal, True, False)

            # toute paire possible d’actions pouvant accomplir ces 2 littéraux est mutex -> se sert des actions précédentes

        # on récupère les actions pouvant donner un littéral (donc littéral dans effect de l'action)
        # on compare les littéraux un à un
            # on regarde toutes les paires d'actions de ces littéraux, on regarde si elles sont toutes mutex

        dict_pos = dict()
        #dict_neg = dict()
        for literal in state.pos:
            dict_pos[literal] = self.get_action(literal, -1, True)
            if 'inc' in literal:
                pass
                #print(dict_pos[literal])

        '''for literal in state.neg:
            dict_neg[literal] = get_action_giving(literal)'''

        for literal1 in state.pos:
            for literal2 in state.pos:
                if literal1 != literal2:
                    if self.is_mutex_literal(dict_pos[literal1], dict_pos[literal2]):
                        #print(literal1)
                        #print(literal2)
                        self.mutex_literal(literal1, literal2, True, True)
        
        '''    for literal2 in state.neg:
                if self.is_mutex_literal(dict_pos[literal1], dict_neg[literal2]):
                    self.mutex_literal(literal1, literal2, True, False)
            
        for literal1 in state.neg:
            for literal2 in state.neg:
                if literal1 != literal2:
                    if self.is_mutex_literal(dict_neg[literal1], dict_neg[literal2]):
                        self.mutex_literal(literal1, literal2, True, True)'''

    def in_state(self, index, goal):
        #print(goal)
        #print(self.literal_mutexes[index - 1])
        if index == 0:
            return True
        for t in self.literal_mutexes[index - 1]:
            if t[0][0] in goal.pos and t[0][1] == True:
                if t[1][0] in goal.pos and t[1][1] == True:
                    print("ici1")
                    return False
                if t[1][0] in goal.neg and t[1][1] == False:
                    print("ici2")
                    return False
            if t[0][0] in goal.neg and t[0][1] == False:
                if t[1][0] in goal.pos and t[1][1] == True:
                    print("ici3")
                    return False
                if t[1][0] in goal.neg and t[1][1] == False:
                    print("ici4")
                    return False
        print("ici")
        return self.in_action_set(index - 1, goal, len(goal.pos) + len(goal.neg) - 1, list())
    
    def check_mutex_action(self, action_set, index):
        for action1 in action_set:
            for action2 in action_set:
                if action1 != action2:
                    for t in self.action_mutexes[index]:
                        if t == (action1, action2) or t == (action1, action2):
                            return True
        return False

    def in_action_set(self, index, goal, index_goal, action_goal):
        # le get_action peut chercher pour un goal négatif
        if index_goal >= len(goal.pos): #négatif
            actions = self.get_action(list(goal.neg)[index_goal - len(goal.pos)], index, False)
        else:
            actions = self.get_action(list(goal.pos)[index_goal], index, True)
        for action in actions:
            action_goal.append(action)
            if index_goal != 0:
                next = self.in_action_set(index, goal, index_goal - 1, action_goal)
                if next != False:
                    return next
            else:
                if not self.check_mutex_action(action_goal, index):
                    new_goal = State(set(), set())
                    for action in action_goal:
                        new_goal.pos.update(action.pre_pos)
                        new_goal.neg.update(action.pre_neg)
                    next = self.in_state(index, new_goal)
                    if next == False:
                        pass
                    elif next == True:
                        return [set(action_goal)]
                    else:
                        return next.append(set(action_goal))
            action_goal.pop()
        return False

        

    def plan(self):
        # On vérifie si le current_state comprend le goal
        # Si oui, on part des littéraux du goal et on remonte avec les mutex
        # Si nos deux littéraux sont mutex alors c'est mort, 
        
        current_state_index = len(self.state_levels) - 1

        if self.goal.pos <= self.state_levels[current_state_index].pos and self.goal.neg <= self.state_levels[current_state_index].neg: # Si oui, on peut commencer à chercher un plan
            plan = self.in_state(current_state_index, self.goal)
            if plan == False:
                print("Pas de plan trouvé")
                return False
            else:
                return plan
        print("Le state ne comprend pas le goal")
        return False

    def graphplan(self):
        res = self.plan()
        while(res == False):
            self.create_next_layer()
            res = self.plan()
        return res

    '''
    def graphplan(self, domain_file, problem_file):
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
    '''
    
    def get_init(self, problem_file):
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

def print_plan(plan):
    i = 0
    for step in plan:
        i += 1
        print("Step n°" + str(i))
        for action in list(step):
            print(action.name)
            print(str(action.pre_pos) + " | " + str(action.pre_neg))
            print()

if __name__ == "__main__":
    
    domain_file = ".\Problems\Groupe3\maze.pddl" #".\Problems\Groupe3\maze.pddl" #sys.argv[1]
    problem_file = '.\Problems\Groupe3\problems\maze_p0.pddl' #'.\Problems\Groupe3\problems\maze_p0.pddl' #sys.argv[2]
    
    graph_plan_object = GraphPlan(domain_file, problem_file)
    plan = graph_plan_object.graphplan()
    
    if plan is None:
        print("No plan found.")
    else:
        print("A plan has been found")
        print()
        print_plan(plan)