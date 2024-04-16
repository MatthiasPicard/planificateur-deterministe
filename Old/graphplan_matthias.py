import pddlpy
import random
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
        init, goal = self.get_init(problem_file)
        self.goal = goal
        self.action_layers = []
        self.prop_layers = [init] # always longer than actions_layers
        self.dp = pddlpy.DomainProblem(domain_file,problem_file)
        self.prop_mutexes = [[]]   # list of list of pairs of mutex propositions (a propostion mutex is of the form ((prop1,is_true),(prop2,is_true)), to keep track of the negations)
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

    def forward(self,actions, state): # pour le backward faut garder une trace de quelles actions ont faites 
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
    
    
    def create_mutexes(self,prop_layer,action_layer,prop_layer_index,action_layer_index):
        
        #1) l’un est la négation de l’autre,
        for i in prop_layer.pos: 
            for j in prop_layer.neg:
                if i == j:
                    self.prop_mutexes[prop_layer_index].append(((i,True),(j,False)))
        for i in prop_layer.neg: 
            for j in prop_layer.pos:
                if i == j:
                    self.prop_mutexes[prop_layer_index].append(((i,False),(j,True)))
                    
        #2) two literals are mutex if every pairs of action that can achieve these two literals are mutex   
        for prop1 in set.union(prop_layer.pos, prop_layer.neg):
            for prop2 in set.union(prop_layer.pos, prop_layer.neg):
                if prop1 != prop2:    
                    accomplish_both_prop = []
                    for action in action_layer:
                        if (prop1 in action.effect_pos or prop1 in action.effect_neg) \
                            and (prop2 in action.effect_pos or prop2 in action.effect_neg):
                            accomplish_both_prop.append(action)
                    mutex = True   
                    for i in range(len(accomplish_both_prop)): # cartesian product?
                        for j in range(i+1,len(accomplish_both_prop)):
                            if not self.is_mutex_action(accomplish_both_prop[i], accomplish_both_prop[j], action_layer_index):
                                mutex = False
                                break
                    if mutex:
                        self.prop_mutexes[prop_layer_index].append((prop1,prop2))
    
        
        for action1 in action_layer: # 3) two actions are mutex if they have inconsistent effects
            for action2 in action_layer:
                if action1 != action2:
                    mutex = False
                    for prop1 in set.union(action1.eff_pos, action1.eff_neg):
                        for prop2 in set.union(action2.eff_pos, action2.eff_neg):
                            if  self.is_mutex_prop(prop1, prop2,prop_layer_index):# we know that since we applied 1) first
                                mutex = True
                                break
                    if mutex:
                        self.action_mutexes[action_layer_index].append((action1,action2))
                    else:  # 4) two actions are mutex if they interfere  
                        for prop1 in action1.precondition_pos:
                            for prop2 in action2.effect_neg:
                                if prop1 == prop2:
                                    self.action_mutexes[action_layer_index].append((action1,action2))
                                else:
                                    for prop1 in action1.precondition_neg:
                                        for prop2 in action2.effect_pos:
                                            if prop1 == prop2:
                                                self.action_mutexes[action_layer_index].append((action1,action2))
                                                       

    def plan(self):
        current_state = State(self.initial_state_pos, self.initial_state_neg)
        goal_state_set = self.goal_state 
        plan = []        
        while current_state.pos != goal_state_set:
            applicable_actions = [
                action for action in self.actions 
                if action.is_applicable(current_state.pos, current_state.neg)
            ]
            if not applicable_actions:
                print("No applicable actions to reach the goal state.")
                return None
            best_action=random.choice(applicable_actions)
            print(best_action.name)
            print(current_state_pos,current_state_neg)
            current_state_pos,current_state_neg = best_action.apply(current_state_pos, current_state_neg)
            print(current_state_pos,current_state_neg)
            # Sélection de l'action avec le plus grand nombre d'effets positifs partagés avec l'état but
            #best_action = max(applicable_actions, key=lambda x: len(set(x.eff_pos) & goal_state_set))
            plan.append(best_action)
            #print(best_action)
            #print(current_state.pos, current_state.neg)

            # Mise à jour de l'état courant après application de la meilleure action
            #current_state = best_action.apply(current_state)

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
                  
    def is_mutex_action(self,action1, action2,action_index):
        set_actions = set([action1, action2])
        return set_actions in [set(elem) for elem in self.action_mutexes[action_index]]
    
    def is_mutex_prop(self,prop1, prop2,prop_index):
        set_props = set([prop1, prop2])
        return set_props in [set(elem) for elem in self.prop_mutexes[prop_index]]

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

        return State(set_str(init_pos_predicates), set_str(init_neg_predicates)),State(set_str(goal_pos_predicates), set_str(goal_neg_predicates))

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
        
if __name__ == "__main__":
    
    domain_file = ".\Problems\Groupe3\maze.pddl"
    problem_file = '.\Problems\Groupe3\problems\maze_p0.pddl'
    
    graph_plan_object = GraphPlan(domain_file, problem_file)
    plan = graph_plan_object.graphplan(domain_file, problem_file)
    
    if plan is None:
        print("No plan found.")
    else:
        print(plan)
    