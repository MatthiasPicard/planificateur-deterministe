'''
Created on Oct 20, 2013

@author: Ofra
'''
from Old.Pair import Pair
import copy
from PropositionLayer import PropositionLayer
from PlanGraph import PlanGraph
from Parser import Parser
from Action import Action
from random import choice


class GraphPlan(object):
    '''
    A class for initializing and running the graphplan algorithm
    '''


    def __init__(self,domain, problem):
        '''
        Constructor
        '''
        self.independentActions = []
        self.noGoods=[]
        self.graph = []
        p = Parser(domain, problem)
        domainKB = p.parseActionsAndPropositions();
        self.actions = domainKB[0]
        self.propositions = domainKB[1]
        prob = p.pasreProblem()
        self.initialState = prob[0]
        self.goal = prob[1]
        self.createNoOps() #creates noOps that are used to propogate existing propositions from one layer to the next
        self.independent() #creates independent actions list
        self.graphplan() #calls graphplan

    '''the graphplan algorithm. If it's easier for you to write your own code, go for it. But you may use this. The code calls the extract function which you should complete below '''
    def graphplan(self):

        #initialization
        initState = self.initialState
        goalState = self.goal
        level = 0
        self.noGoods = [] #make sure you update noGoods in your backward search!
        self.noGoods.append([])

        #create first layer of the graph, note it only has a proposition layer which consists of the initial state.
        propLayerInit = PropositionLayer()
        for prop in initState:
            propLayerInit.addProposition(prop)
        pgInit = PlanGraph(0, self.independentActions)
        pgInit.setPropositionLayer(propLayerInit)
        self.graph.append(pgInit)

        '''while the layer does not contain all of the propositions in the goal state, or some of these propositions are mutex in the layer we, and we have not reached the fixed point, continue expanding the graph'''
        while((self.goalStateNotInPropLayer(goalState, self.graph[level].getPropositionLayer().getPropositions()) | self.goalStateHasMutex(goalState, self.graph[level].getPropositionLayer())) & (self.Fixed(level)==False)):
            self.noGoods.append([])
            level = level +1
            pgNext = PlanGraph(level, self.independentActions) #create new PlanGraph object
            pgNext.expand(self.graph[level-1], self.propositions, self.actions) #calls the expand function, which you are implementing in the PlanGraph class
            self.graph.append(copy.deepcopy(pgNext)) #appending the new level to the plan graph

        if (self.goalStateNotInPropLayer(goalState, self.graph[level].getPropositionLayer().getPropositions()) | self.goalStateHasMutex(goalState, self.graph[level].getPropositionLayer())):
            print 'could not find a plan'
            return None #this means we stopped the while loop above because we reached a fixed point in the graph. nothing more to do, we failed!

        sizeNoGood = len(self.noGoods[level]) #remember size of nogood table

        plan = self.extract(self.graph, goalState, level) #try to extract a plan since all of the goal propositions are in current graph level, and are not mutex
        while(plan==None): #while we didn't extract a plan successfully
            level = level+1
            self.noGoods.append([])
            pgNext = PlanGraph(level, self.independentActions) #create next level of the graph by expanding
            pgNext.expand(self.graph[level-1], self.propositions, self.actions) #create next level of the graph by expanding
            self.graph.append(copy.deepcopy(pgNext))
            plan = self.extract(self.graph, goalState, level) #try to extract a plan again
            if ((plan==None) & (self.Fixed(level))): #if failed and reached fixed point
                if sizeNoGood==len(self.noGoods[level]): #if size of nogood didn't change, means there's nothing more to do. We failed.
                    print 'could not find a plan'
                    return None
                sizeNoGood=len(self.noGoods[level]) #we didn't fail yet! update size of no good
        print "final plan"
        for act in plan:
            print act
        return plan

    def extract(self, Graph, subGoals, level):
        '''YOUR CODE HERE: you should implement the backsearch part of graphplan that tries to extract a plan when all goal propositions exist in a graph plan level. you can write additional helper functions'''
        if level == 0:
            return []
        #if set(subGoals) in [set(x) for x in self.noGoods[level]]:
        if all(g in self.noGoods[level] for g in subGoals):
            return None
        plan = self.gpSearch(Graph, subGoals, [], level)
        if plan != None:
            return plan
        self.noGoods[level] = self.noGoods[level] + subGoals
        return None

        pass

    def gpSearch(self, Graph, subGoals, plan, level):
        # graph is a list of planGraphs
        # subGoals is a list of propositions
        # plan is a list of actions
        '''YOUR CODE HERE: you don't have to use this, but you might consider having this function and calling it from extract. The functions can call each other recursively to find the plan. You don't have to use this'''
        if subGoals == []:
            newSubGoals = []
            for p in plan:
                newSubGoals += p.getPre()
            newPlan = self.extract(Graph, newSubGoals, level-1)
            if newPlan == None:
                return None
            else:
                return newPlan + plan
        p = choice(subGoals)
        #p = subGoals[0]
        providers = [a for a in Graph[level].getActionLayer().getActions() if (a.isPosEffect(p)
        and not any(Graph[level].getActionLayer().isMutex(Pair(a, x)) for x in plan))]
        if providers == []:
            return None

        for a in providers:
            result = self.gpSearch(Graph, [item for item in subGoals if item not in a.getAdd()], plan + [a], level)
            if result != None:
                return result
        return None

    '''helper function that checks whether all propositions of the goal state are in the current graph level'''
    def goalStateNotInPropLayer(self, goalState, propositions):
        for goal in goalState:
            if goal not in propositions:
                return True
        return False
    '''helper function that checks whether all goal propositions are non mutex at the current graph level'''
    def goalStateHasMutex(self, goalSate, propLayer):
        for goal1 in goalSate:
            for goal2 in goalSate:
                if propLayer.isMutex(goal1,goal2):
                    return True
        return False

    '''checks if we have reached a fixed point, i.e. each level we'll expand would be the same, thus no point in continuting'''
    def Fixed(self, level):
        if level==0:
            return False

        if (len(self.graph[level].getPropositionLayer().getPropositions()) == len(self.graph[level-1].getPropositionLayer().getPropositions())):
            if (len(self.graph[level].getPropositionLayer().getMutexProps()) == len(self.graph[level-1].getPropositionLayer().getMutexProps())):
                return True
        return False

    '''creates the noOps that are used to propogate propositions from one layer to the next'''
    def createNoOps(self):
        for prop in self.propositions:
            name = prop.name
            precon = []
            add = []
            precon.append(prop)
            add.append(prop)
            delete = []
            act = Action(name,precon,add,delete)
            self.actions.append(act)
            prop.addProducer(act)

    '''creates a list of independent actions'''
    def independent(self):
        for act1 in self.actions:
            for act2 in self.actions:
                if(self.independentPair(act1,act2)):
                    self.independentActions.append(Pair(act1,act2))


    def independentPair(self, a1, a2):
        if a1==a2:
            return True
        for prop in a1.getDelete():
            if (a2.isPreCond(prop) | a2.isPosEffect(prop)):
                return False
        for prop in a2.getDelete():
            if (a1.isPreCond(prop) | a1.isPosEffect(prop)):
                return False
        return True

    def isIndependent(self, a1, a2):
        return Pair(a1,a2) in self.independentActions

    '''Helper action that you may want to use when extracting plans, returns true if there are no mutex actions in the plan'''
    def noMutexActionInPlan(self, plan, act, actionLayer):
        for planAct in plan:
            if actionLayer.isMutex(Pair(planAct,act)):
                return False
        return True

if __name__ == '__main__':
    domain = 'dwrDomain.txt'
    problem = 'dwrProblem4.txt'
    gp = GraphPlan(domain, problem)

