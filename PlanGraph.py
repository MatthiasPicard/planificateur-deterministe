'''
Created on Oct 20, 2013

@author: Ofra
'''
from Action import Action
from ActionLayer import ActionLayer
from Pair import Pair
from Proposition import Proposition
from PropositionLayer import PropositionLayer
from itertools import combinations

class PlanGraph(object):
    '''
    A class for representing a level in the plan graph. For each level i, the PlanGraph consists of the actionLayer and propositionLayer at this level
    '''


    def __init__(self, level, independentActions):
        '''
        Constructor
        '''
        self.level = level
        self.independentActions = independentActions # a list of the independent actions (this would be the same at each level)
        self.actionLayer = ActionLayer()
        self.propositionLayer = PropositionLayer();

    def getPropositionLayer(self):
        return self.propositionLayer

    def setPropositionLayer(self, propLayer):
        self.propositionLayer = propLayer

    def getActionLayer(self):
        return self.actionLayer

    def setActionLayer(self, actionLayer):
        self.actionLayer = actionLayer

    # expands G_(k-1), graph from previous layer
    def expand(self, previousLevel, allProps, allActions): #you can change the params the function takes if you like
        '''YOUR CODE HERE'''
        # gets things first so we don't get them over and over in our list comprehensions
        previousPropLayer = previousLevel.getPropositionLayer()
        previousActionLayer = previousLevel.getActionLayer()
        previousActions = previousActionLayer.getActions()

        previousProps = previousPropLayer.getPropositions()
        previousMutexProps = previousPropLayer.getMutexProps()

        A_k = ActionLayer()
        ###### this is for A_k (actions in next layer)
        for a in allActions:
            if (all(p in previousProps for p in a.getPre()) 
                and not any(previousPropLayer.isMutex(p1, p2) for p1, p2 in combinations(a.getPre(), 2))):
                A_k.addAction(a)

        ###### this is for mA_k (mutex actions in next layer)
        currentActions = A_k.getActions()
        for a1, a2 in combinations(currentActions, 2):
            if a1 != a2 and previousLevel.mutexActions(a1, a2, previousMutexProps):
                A_k.addMutexActions(a1, a2)

        self.setActionLayer(A_k)

        ###### this is for Pk (propositions in next layer)
        P_k = PropositionLayer()
        for p in allProps:
            if any(a.isPosEffect(p) for a in currentActions):
                P_k.addProposition(p)
        
        ###### this is for mPk (mutex propositions in next layer)
        A_k = self.getActionLayer()
        for p1, p2 in combinations(P_k.getPropositions(), 2):
            if p1 != p2 and self.mutexPropositions(p1, p2, A_k.getMutexActions()):
                P_k.addMutexProp(p1, p2)
        self.setPropositionLayer(P_k)

        return

    def mutexActions(self, a1, a2, mutexProps):
        '''YOUR CODE HERE: complete code for deciding whether actions a1 and a2 are mutex, given the previous proposition layer. Your exapnd function should call this function'''
        if Pair(a1,a2) not in self.independentActions:
            return True
        for p1 in a1.getPre():
            for p2 in a2.getPre():
                if Pair(p1,p2) in mutexProps:
                    return True
        return False

    def mutexPropositions(self, prop1, prop2, mutexActions):
        '''YOUR CODE HERE: complete code for deciding whether propositions p1 and p2 are mutex, given the previous proposition layer. Your exapnd function should call this function'''
        for a1 in [p for p in prop1.getProducers() if p in self.getActionLayer().getActions()]:
        #for a1 in prop1.getProducers():
            #for a2 in prop2.getProducers():
            for a2 in [p for p in prop2.getProducers() if  p in self.getActionLayer().getActions()]:
                if Pair(a1,a2) not in mutexActions:
                    return False
        return True