import pddlpy
import os

# si deux actions sont mutex dans Ai alors elles le sont à tous les niveaux inférieurs
# si deux littéraux ne sont pas mutex dans Si alors ils ne le seront jamais



def is_applicable(action, state):
    predicates = [elem.predicate for elem in state]
    return all(list(pre) in predicates for pre in action.precondition_pos)

def apply_action(action, state):
    # new_state = state.copy()
    # new_state.update(action.effect_pos)
    # new_state.difference_update(action.effect_neg) # ne fait rien jsp pk
    # return new_state

    new_state = state.copy()
    for effect in action.effect_pos:
        new_state.add(effect)
    for effect in action.effect_neg:
        new_state.discard(effect)
    return new_state

def total_state(actions,state):
    liste_actions = [] # une action peut être effectué sur des objets différents dans un état donné
    for action in actions:
        if is_applicable(action, state):
            liste_actions.append(apply_action(action, state))
    return liste_actions

def get_pairs(layer):
    # Generate all possible pairs of actions/literals in the level
    pairs = []
    for a1 in layer:
        for a2 in layer:
            if a1 != a2:
                pairs.append((a1, a2))
    return pairs

def are_mutex(a1, a2, layer):
    # Check if two actions/literals are mutex in the given level
    return (a1 in layer and a2 in layer) and (inconsistent_effects(a1, a2, layer) or interference(a1, a2, layer))


def inconsistent_effects(a1, a2, layer):
    # Check if the effects of two actions are inconsistent
    return any(eff.negate() in layer[a2] for eff in layer[a1].neg_effects)


def interference(a1, a2, layer):
    # Check if two actions have interfering preconditions
    return any(p.negate() in layer[a2] for p in layer[a1].pos_effects)


def is_mutex(a, s, layer, mutexes):
    # Check if an action/literal is mutex with all elements in a state
    return any(a in mutexes[e] for e in s)

def update_mutexes(layer, mutexes):
    for pair in get_pairs(layer):
        if are_mutex(pair[0], pair[1], layer):
            mutexes[pair[0]].add(pair[1])
            mutexes[pair[1]].add(pair[0])

def is_plan(state):
    return 0

path = 'plannificateur-deterministe/Problems/Groupe3'
# Test the graphplan algorithm on the provided robot problem
domain_file = os.path.join(path, 'maze.pddl')
problem_file = os.path.join(path, 'problems/maze_p0.pddl')
domainpb = pddlpy.DomainProblem(domain_file, problem_file)

state = domainpb.initialstate()
actions = list(domainpb.operators())
domainpb.ground_operator('move-down')

get_possible_actions = lambda s : [0]
get_next_states = lambda s, a : [0]

init_state = ((0,0), (1,1)) #[]
goal_state = ((4,4))

is_plan = lambda s: True if s==goal_state else False

seen_states = {f"state_{i}": state for i, state in enumerate(init_state)}
seen_actions = {}
mutex_state = []
init_layer = [state for state in init_state]
layers = [init_layer]
actions = []
k = 500
current_layer = init_layer
for i in range(k):
    if is_plan(current_layer):
        break
    next_layer = []
    for state in current_layer:
        
        next_states = []
        curr_actions = []
        for action in actions:
            action_op = domainpb.ground_operator(action)
            next_state, applied_action = total_state(action_op, state)
            if next_state :
                next_states.extend(next_state)
                curr_actions.extend(applied_action)

            



