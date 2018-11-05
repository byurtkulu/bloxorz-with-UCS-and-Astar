

'''
Bahadır Yurtkulu
19745

'''



"""Search (Chapters 3-4)

The way to use this code is to subclass Problem to create a class of problems,
then create problem instances and solve them with calls to the various search
functions."""

from utils import (
    memoize, PriorityQueue, is_in, argmin, argmax, argmax_random_tie, probability, weighted_sampler, print_table, open_data
)

from collections import defaultdict, deque
import math
import random
import sys
import bisect
from operator import itemgetter

from memory_profiler import profile
import numpy as np
import time
import pandas as pd
import matplotlib.pyplot as plt 

infinity = float('inf')

# _____________________________________________________________________________

class State:
    # s1 and s2 are coordinates(lists) not tuples because tuples are immutable. 
    def __init__(self, s1, s2):
        self.s1 = s1
        self.s2 = s2
    
    def __eq__(self, other):
        return self.s1 == other.s1 and self.s2 == other.s2 or self.s1 == other.s2 and self.s2 == other.s1

class BloxorzMap:
    # Our map of Bloxorz
    def __init__(self, matrix):
        self.matrix = matrix

# _____________________________________________________________________________

# inherits BloxorzMap
class Problem(BloxorzMap):

    """The abstract class for a formal problem. You should subclass
    this and implement the methods actions and result, and possibly
    __init__, goal_test, and path_cost. Then you will create instances
    of your subclass and solve them with the various search functions."""

    def __init__(self, matrix, initial, goal=None):
        """The constructor specifies the initial state, and possibly a goal
        state, if there is a unique goal. Your subclass's constructor can add
        other arguments."""
        BloxorzMap.__init__(self, matrix)
        self.initial = initial
        self.goal = goal
        

    def actions(self, state):
        """Return the actions that can be executed in the given
        state. The result would typically be a list, but if there are
        many actions, consider yielding them one at a time in an
        iterator, rather than building them all at once."""

        # Returning only north south etc is not efficient. 
        # So this will return the actions tupled with next states: 
        # (direction, state)
        # Return function will read this tuple and will return state


        # coordinates after actions.
        north_s1 = []
        north_s2 = []
        south_s1 = []
        south_s2 = []
        west_s1 = []
        west_s2 = []
        east_s1 = []
        east_s2 = []

        # Possible actions and resulting states.

        # s1,s2 overlaps
        if state.s1 == state.s2:
            north_s1 = [state.s1[0]-1, state.s1[1]]
            north_s2 = [state.s2[0]-2, state.s2[1]]

            south_s1 = [state.s1[0]+1, state.s1[1]]
            south_s2 = [state.s2[0]+2, state.s2[1]]

            west_s1 = [state.s1[0], state.s1[1]-1]
            west_s2 = [state.s1[0], state.s2[1]-2]

            east_s1 = [state.s1[0], state.s1[1]+1]
            east_s2 = [state.s2[0], state.s2[1]+2]
        
        else:
            # move both s1,s2 one tile up, down, right or left.
            north_s1 = [state.s1[0]-1, state.s1[1]]
            north_s2 = [state.s2[0]-1, state.s2[1]]
            
            south_s1 = [state.s1[0]+1, state.s1[1]]
            south_s2 = [state.s2[0]+1, state.s2[1]]

            west_s1 = [state.s1[0], state.s1[1]-1]
            west_s2 = [state.s2[0], state.s2[1]-1]

            east_s1 = [state.s1[0], state.s1[1]+1]
            east_s2 = [state.s2[0], state.s2[1]+1]

            # NORTH
            # s1 is souther?    ||
            if north_s1[0] == state.s2[0]:
                north_s1[0] -= 1
            # s2 is souther?    ||
            elif north_s2[0] == state.s1[0]:
                north_s2[0] -= 1
            # else they are horizontal. Do nothing. ==

            # SOUTH
            # s1 is norther? ||
            if south_s1[0] == state.s2[0]:
                south_s1[0] += 1
            # s2 is norther? ||
            elif south_s2[0] == state.s1[0]:
                south_s2[0] += 1
            # Else horizontal
        
            # WEST
            # s1 on the south.
            if west_s1[1] == state.s2[1]:
                west_s1[1] -= 1
            # s2 on the south
            elif west_s2[1] == state.s1[1]:
                west_s2[1] -= 1
            # else the block is vertical ||

            # EAST
            # s1 is on the west
            if east_s1[1] == state.s2[1]:
                east_s1[1] += 1
            #s2 on the west
            elif east_s2[1] == state.s1[1]:
                east_s2[1] += 1
            #else it is vertical ||
        

        act = [] #keep actions with the resulting states.


        #Validity test for the actions. 

        height = len(self.matrix)
        width = len(self.matrix[0])

        
        # check if one of the 'S's is outside of the map.
        #NORTH
        north_map_constraint = north_s1[0] in range(height) and north_s2[0] in range(height) and north_s1[1] in range(width) and north_s2[1] in range(width)
        
        # SOUTH
        south_map_constraint = south_s1[0] in range(height) and south_s2[0] in range(height) and south_s1[1] in range(width) and south_s2[1] in range(width)

        # WEST
        west_map_constraint = west_s1[0] in range(height) and west_s2[0] in range(height) and west_s1[1] in range(width) and west_s2[1] in range(width)

        # EAST
        east_map_constraint = east_s1[0] in range(height) and east_s2[0] in range(height) and east_s1[1] in range(width) and east_s2[1] in range(width)
        
        # check for any overlapping X
        
        north_valid = north_map_constraint and self.matrix[north_s1[0]][north_s1[1]] != 'X' and self.matrix[north_s2[0]][north_s2[1]] != 'X'
        
        south_valid = south_map_constraint and self.matrix[south_s1[0]][south_s1[1]] != 'X' and self.matrix[south_s2[0]][south_s2[1]] != 'X'        
        
        west_valid = west_map_constraint and self.matrix[west_s1[0]][west_s1[1]] != 'X' and self.matrix[west_s2[0]][west_s2[1]] != 'X'
        
        east_valid = east_map_constraint and self.matrix[east_s1[0]][east_s1[1]] != 'X' and self.matrix[east_s2[0]][east_s2[1]] != 'X'

        #append to the list if they satisfy the rules.
        if north_valid:
            north_state = [north_s1, north_s2]
            act.append(north_state)
        
        if south_valid:
            south_state = [south_s1, south_s2]
            act.append(south_state)
        
        if west_valid:
            west_state = [west_s1, west_s2]
            act.append(west_state)
        
        if east_valid:
            east_state = [east_s1, east_s2]
            act.append(east_state)
        
        # actions list is ready. It consists of possible actions tupled with next states.

        return act


    def result(self, state, action):
        """Return the state that results from executing the given
        action in the given state. The action must be one of
        self.actions(state)."""
        return State(action[0], action[1])
 
    def goal_test(self, state):
        """Return True if the state is a goal. The default method compares the
        state to self.goal or checks for state in self.goal if it is a
        list, as specified in the constructor. Override this method if
        checking against a single self.goal is not enough."""
        if isinstance(self.goal, list):
            return is_in(state, self.goal)
        else:
            return state == self.goal

    def path_cost(self, c, state1, action, state2):
        """Return the cost of a solution path that arrives at state2 from
        state1 via action, assuming cost c to get up to state1. If the problem
        is such that the path doesn't matter, this function will only look at
        state2.  If the path does matter, it will consider c and maybe state1
        and action. The default method costs 1 for every step in the path."""
        
        # Manhattan distance to the initial state.

        # manhattan distance of s1,s2 to the goal state1
        '''
        # State 1 to initial
        state1_L1 = abs(state1.s1[0] - self.initial.s1[0]) + abs(state1.s1[1] - self.initial.s1[1])
        state1_L2 = abs(state1.s2[0] - self.initial.s2[0]) + abs(state1.s2[1] - self.initial.s2[1])
        dist_state1 = max(state1_L1, state1_L2)

        # State 2 to initial
        state2_L1 = abs(state2.s1[0] - self.initial.s1[0]) + abs(state2.s1[1] - self.initial.s1[1])
        state2_L2 = abs(state2.s2[0] - self.initial.s2[0]) + abs(state2.s2[1] - self.initial.s2[1])
        dist_state2 = max(state2_L1, state2_L2)
        '''
        return c + 1 #abs(dist_state1 - dist_state2)

    def value(self, state):
        """For optimization problems, each state has a value.  Hill-climbing
        and related algorithms try to maximize this value."""
        raise NotImplementedError

    def h(self, node):
        """ Return the heuristic value for a given state. 
        Manhattan distance is used. L1 = |x1-x2|+|y1-y2|. 
        Manhattan distance of s1,s2 to the goal states are as follows: """

        L1 = abs(node.state.s1[0] - self.goal.s1[0]) + abs(node.state.s1[1] - self.goal.s1[1])
        L2 = abs(node.state.s2[0] - self.goal.s2[0]) + abs(node.state.s2[1] - self.goal.s2[1])

        return max(L1,L2)/2 # to make it admissable



# ______________________________________________________________________________


class Node:

    """A node in a search tree. Contains a pointer to the parent (the node
    that this is a successor of) and to the actual state for this node. Note
    that if a state is arrived at by two paths, then there are two nodes with
    the same state.  Also includes the action that got us to this state, and
    the total path_cost (also known as g) to reach the node.  Other functions
    may add an f and h value; see best_first_graph_search and astar_search for
    an explanation of how the f and h values are handled. You will not need to
    subclass this class."""

    def __init__(self, state, parent=None, action=None, path_cost=0):
        """Create a search tree Node, derived from a parent by an action."""
        self.state = state
        self.parent = parent
        self.action = action
        self.path_cost = path_cost
        self.depth = 0
        if parent:
            self.depth = parent.depth + 1

    def __repr__(self):
        return "<Node {}>".format(self.state)

    def __lt__(self, node):
        return self.path_cost < node.path_cost ##  this was state. Changed to path_cost


    def expand(self, problem):
        """List the nodes reachable in one step from this node."""
        return [self.child_node(problem, action)
                for action in problem.actions(self.state)]

    def child_node(self, problem, action):
        """[Figure 3.10]"""
        next_state = problem.result(self.state, action)
        next_node = Node(next_state, self, action,
                    problem.path_cost(self.path_cost, self.state,
                                      action, next_state))
        return next_node
    
    def solution(self):
        """Return the sequence of actions to go from the root to this node."""
        return [node.action for node in self.path()[1:]]

    def path(self):
        """Return a list of nodes forming the path from the root to this node."""
        node, path_back = self, []
        while node:
            path_back.append([node.state.s1, node.state.s2]) # EDITED
            node = node.parent
        return list(reversed(path_back))

    # We want for a queue of nodes in breadth_first_graph_search or
    # astar_search to have no duplicated states, so we treat nodes
    # with the same state as equal. [Problem: this may not be what you
    # want in other contexts.]

    def __eq__(self, other):
        return isinstance(other, Node) and self.state == other.state

    def __hash__(self):
        return hash(self.state)

# ______________________________________________________________________________

def best_first_graph_search(problem, f):
    """Search the nodes with the lowest f scores first.
    You specify the function f(node) that you want to minimize; for example,
    if f is a heuristic estimate to the goal, then we have greedy best
    first search; if f is node.depth then we have breadth-first search.
    There is a subtlety: the line "f = memoize(f, 'f')" means that the f
    values will be cached on the nodes as they are computed. So after doing
    a best first search you can examine the f values of the path returned."""
    f = memoize(f, 'f')
    node = Node(problem.initial)
    frontier = PriorityQueue('min', f)
    frontier.append(node)
    explored = []

    while frontier:
        node = frontier.pop()
        if problem.goal_test(node.state):
            print("Solution state: ", node.state.s1, node.state.s2)
            print("cost:", node.path_cost)
            print(node.path())
            return node
        explored.append(node.state)
        for child in node.expand(problem):
            if child.state not in explored and child not in frontier:
                frontier.append(child)
            elif child in frontier:
                incumbent = frontier[child]
                if f(child) < f(incumbent):
                    del frontier[incumbent]
                    frontier.append(child)

    return None

@profile
def uniform_cost_search(problem):
    """[Figure 3.14]"""
    return best_first_graph_search(problem, lambda node: node.path_cost)


greedy_best_first_graph_search = best_first_graph_search
# Greedy best-first search is accomplished by specifying f(n) = h(n).

@profile
def astar_search(problem, h=None):
    """A* search is best-first graph search with f(n) = g(n)+h(n).
    You need to specify the h function when you call astar_search, or
    else in your Problem subclass."""
    h = memoize(h or problem.h, 'h')
    return best_first_graph_search(problem, lambda n: n.path_cost + h(n))



def main():
    
    level_one = [
    ['O','O','O','X','X','X','X','X','X','X'],
    ['O','S','O','O','O','O','X','X','X','X'],
    ['O','O','O','O','O','O','O','O','O','X'],
    ['X','O','O','O','O','O','O','O','O','O'],
    ['X','X','X','X','X','O','O','G','O','O'],
    ['X','X','X','X','X','X','O','O','O','X']]

    level_two = [
    ['X','X','X','X','X','X','O','O','O','O','O','O','O','X','X'],
    ['O','O','O','O','X','X','O','O','O','X','X','O','O','X','X'],
    ['O','O','O','O','O','O','O','O','O','X','X','O','O','O','O'],
    ['O','S','O','O','X','X','X','X','X','X','X','O','O','G','O'],
    ['O','O','O','O','X','X','X','X','X','X','X','O','O','O','O'],
    ['X','X','X','X','X','X','X','X','X','X','X','X','O','O','O']]

    s1_one = [1,1]
    s2_one = [1,1]
    g_one = [4,7]

    s1_two = [3,1]
    s2_two = [3,1]
    g_two = [3,13]
    
    initial_one = State(s1_one, s2_one)
    goal_one = State(g_one, g_one)

    initial_two = State(s1_two, s2_two)
    goal_two = State(g_two, g_two)

    problem_one = Problem(level_one, initial_one, goal_one)
    problem_two = Problem(level_two, initial_two, goal_two)


    run_times = {}

    print("\n\n#####################################################")
    print("#############   AI Bloxorz Problem   ################")
    print("#####################################################\n\n")

    print("LEVELS\n------\n")
    print("Level One: \n", np.matrix(level_one))
    print("Level Two: \n", np.matrix(level_two))
    print("\n******************************************************************"*2)
# ---------------------------------------------------------------
    print("\nUCS FOR LEVEL ONE:")
    start = time.time()
    uniform_cost_search(problem_one)
    end =time.time()
    print("Time: ", end-start)
    run_times['ucs_lev1'] = end-start

    print("\n****************************************************************"*2)
    
    print("\nUCS FOR LEVEL TWO:")
    start = time.time()
    uniform_cost_search(problem_two)
    end = time.time()
    print("Time: ", end-start)
    run_times['ucs_lev2'] = end-start
    
    print("\n****************************************************************"*2)
    
    print("\nA* FOR LEVEL ONE:")
    start = time.time()
    astar_search(problem_one)
    end = time.time()
    print("Time: ", end-start)
    run_times['A*_lev1'] = end-start

    print("\n****************************************************************"*2)

    print("\nA* FOR LEVEL TWO:")
    start = time.time()
    astar_search(problem_two)
    end = time.time()
    print("Time: ", end-start)
    run_times['A*_lev2'] = end-start

    print("Run times: \n", run_times)
    
if __name__ == "__main__":
    main()