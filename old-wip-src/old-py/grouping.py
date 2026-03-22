import random
from itertools import combinations
import copy

def powerset(s):
    powerset = list()
    for r in range(1,len(s)+1):
        powerset = powerset + list(combinations(s, r))
    return [frozenset(x) for x in powerset]

def problemprinter(problem):
    if problem == 'UNSTABLE':
        print 'UNSTABLE'
    else:
        print '\n OUTGOING PROPOSALS:'
        for agent in problem['agents']:
            for out in problem['out_proposals'][agent]:
                print agent, "  --->  ",out

def prefprinter(problem):
    if problem == 'UNSTABLE':
        print 'UNSTABLE'
    else:
        print '\n PREFERENCES:'
        for agent in problem['agents']:
            print agent, ': ',problem['prefs'][agent]

def generate(num):
    agents = list()
    prefs = dict()
    for i in range(0,num):
        agents.append('a' + str(i+1))
    power = powerset(agents)
    for a in agents:
        poss = [x for x in power if a in x]
        poss.remove(set([a]))
        random.shuffle(poss)
        prefs[a]=poss
    out_proposals = dict()
    in_proposals = dict() #form: {'from':set(),'what':set()}
    for a in agents:
        out_proposals[a] = []
        in_proposals[a] = []
    return {'agents':agents,'prefs':prefs,'in_proposals':in_proposals,'out_proposals':out_proposals,'forced_moves':[]}#,'eliminated':[]}


def eliminate(problem, to_eliminate):
    for trash in to_eliminate:
        for a in trash:
            problem['prefs'][a].remove(trash)
            if trash in problem['out_proposals'][a]:
                problem['out_proposals'][a].remove(trash)
            for prop in problem['in_proposals'][a]:
                if prop['what']==trash:
                    problem['in_proposals'][a].remove(prop)
    return problem


###RECURSION

COUNTER = 0

def recurse(problem, J):
    finished = False
    problem['forced_moves'].append(J)
    while not finished:
        finished = True
        for a in problem['agents']:
            has_proposed = set(problem['out_proposals'][a]).difference(set(problem['forced_moves']))
            if has_proposed != set():
                continue
            finished = False
            applicable_prefs = [x for x in problem['prefs'][a] if x not in problem['out_proposals'][a]]
            if applicable_prefs == []:
                return "UNSTABLE"  # SOMEONE RAN OUT - CANT MOVE ON
            H = applicable_prefs[0]
            problem['out_proposals'][a].append(H)
            for b in H.difference(set([a])):
                if problem['in_proposals'][b] == []: #NOT RECEIVED ANY OFFER YET
                    problem['in_proposals'][b].append({'from':set([a]),'what':H})
                    if (len(H)==2): #CONSIDERED (OTHERS REJECTED)
                        offer_pref = problem['prefs'][b].index(H)
                        to_eliminate = [s for s in problem['prefs'][b][offer_pref+1:]]
                        problem = eliminate(problem,to_eliminate)
                else:
                    already_in = 'NA'
                    for i in range(0,len(problem['in_proposals'][b])):
                        held = problem['in_proposals'][b][i]
                        if held['what']==H:
                            already_in = i
                    if already_in == 'NA': #NOT RECEIVED SUCH OFFER YET
                        problem['in_proposals'][b].append({'from':set([a]),'what':H})
                        became_cons = (len(H)==2)
                    else:
                        problem['in_proposals'][b][already_in]['from'] = problem['in_proposals'][b][already_in]['from'].union(set([a]))
                        became_cons = (len(problem['in_proposals'][b][already_in]['from']) == len(H)-1)
                    if became_cons == True: #CONSIDERED (OTHERS REJECTED)
                        offer_pref = problem['prefs'][b].index(H)
                        to_eliminate = [s for s in problem['prefs'][b][offer_pref+1:]]
                        problem = eliminate(problem,to_eliminate)
        if finished:
            for a in problem['agents']:
                applicable_prefs = [x for x in problem['prefs'][a] if x not in problem['out_proposals'][a]]
                if len(applicable_prefs)>0:
                    finished = False
                    K = problem['out_proposals'][a][-1]
                    probing = copy.deepcopy(problem)
                    answer = recurse(probing,K)
                    if answer == 'UNSTABLE':
                        problem = eliminate(problem,applicable_prefs)
                        break
                    else:
                        problem = answer
                        break
    return problem


###CREATE FUNCTION TO TEST STABILITY

def stable(problem,solution):
    if solution == 'UNSTABLE':
        return 'NO STABLE SOLUTION'
    agents = problem['agents']
    problem = problem['prefs']
    solution = solution['prefs']
    for a in agents:
        l = solution[a]
        if len(l)!=1:
            print l
            return 'NOT SOLVED'
    for a in agents:
        solution_rank = problem[a].index(solution[a][0])
        for better in problem[a][0:solution_rank]:
            wrong = True
            for b in better:
                b_solution_rank = problem[b].index(solution[b][0])
                b_better_rank = problem[b].index(better)
                if b_better_rank > b_solution_rank:
                    wrong = False
                    break
            if wrong:
                return 'NOT STABLE'
    return 'STABLE'


###TEST FROM PAPER EXAMPLE 
'''
problem = generate(5)
problem["prefs"]={"a1":[frozenset(["a1","a4"]), frozenset(["a1","a2","a4"]), frozenset(["a1","a3"]), frozenset(["a1","a2","a5"]), frozenset(["a1","a2"])],"a2":[frozenset(["a2","a1","a5"]), frozenset(["a2","a1","a4"]), frozenset(["a2","a1"]), frozenset(["a2","a3"])],"a3":[frozenset(["a3","a5"]), frozenset(["a3","a1"]), frozenset(["a3","a2"]), frozenset(["a3","a4"])],"a4":[frozenset(["a4","a3"]), frozenset(["a4","a1","a2"]), frozenset(["a4","a1"]), frozenset(["a4","a5"])],"a5":[frozenset(["a5","a4"]), frozenset(["a5","a1","a2"]), frozenset(["a5","a3"])]}

problem = recurse(problem,frozenset())

problemprinter(problem)
'''

### DIFFERENT CASES
'''
test1 = {'in_proposals': {'a1': [], 'a3': [], 'a2': [], 'a4': []}, 'forced_moves': [], 'prefs': {'a1': [frozenset(['a1', 'a2']), frozenset(['a1', 'a3', 'a4']), frozenset(['a1', 'a4']), frozenset(['a1', 'a2', 'a4']), frozenset(['a1', 'a3', 'a2']), frozenset(['a1', 'a3']), frozenset(['a1', 'a3', 'a2', 'a4'])], 'a3': [frozenset(['a1', 'a3', 'a4']), frozenset(['a1', 'a3', 'a2']), frozenset(['a3', 'a2']), frozenset(['a1', 'a3', 'a2', 'a4']), frozenset(['a3', 'a4']), frozenset(['a1', 'a3']), frozenset(['a3', 'a2', 'a4'])], 'a2': [frozenset(['a1', 'a2', 'a4']), frozenset(['a1', 'a3', 'a2', 'a4']), frozenset(['a3', 'a2', 'a4']), frozenset(['a1', 'a3', 'a2']), frozenset(['a2', 'a4']), frozenset(['a1', 'a2']), frozenset(['a3', 'a2'])], 'a4': [frozenset(['a1', 'a4']), frozenset(['a3', 'a2', 'a4']), frozenset(['a3', 'a4']), frozenset(['a1', 'a3', 'a4']), frozenset(['a1', 'a3', 'a2', 'a4']), frozenset(['a2', 'a4']), frozenset(['a1', 'a2', 'a4'])]}, 'agents': ['a1', 'a2', 'a3', 'a4'], 'out_proposals': {'a1': [], 'a3': [], 'a2': [], 'a4': []}}

test2 = {'in_proposals': {'a1': [], 'a3': [], 'a2': []}, 'prefs': {'a1': [frozenset(['a1', 'a2']), frozenset(['a1', 'a3', 'a2']), frozenset(['a1', 'a3'])], 'a3': [frozenset(['a1', 'a3']), frozenset(['a1', 'a3', 'a2']), frozenset(['a3', 'a2'])], 'a2': [frozenset(['a3', 'a2']), frozenset(['a1', 'a3', 'a2']), frozenset(['a1', 'a2'])]}, 'forced_moves': [], 'out_proposals': {'a1': [], 'a3': [], 'a2': []}, 'agents': ['a1', 'a2', 'a3']}

test3 = {'in_proposals': {'a1': [], 'a3': [], 'a2': []}, 'prefs': {'a1': [frozenset(['a1', 'a3', 'a2']), frozenset(['a1', 'a3']), frozenset(['a1', 'a2'])], 'a3': [frozenset(['a1', 'a3', 'a2']), frozenset(['a3', 'a2']), frozenset(['a1', 'a3'])], 'a2': [frozenset(['a3', 'a2']), frozenset(['a1', 'a2']), frozenset(['a1', 'a3', 'a2'])]}, 'forced_moves': [], 'out_proposals': {'a1': [], 'a3': [], 'a2': []}, 'agents': ['a1', 'a2', 'a3']}



prefprinter(test1)
problemprinter(recurse(test1,frozenset()))
prefprinter(test2)
problemprinter(recurse(test2,frozenset()))
prefprinter(test3)
problemprinter(recurse(test3,frozenset()))
'''
###TEST A LOT

'''
test= []

for i in range(100):
    test.append(generate(7))


for tester in test:
    prob = copy.deepcopy(tester)
    tester = recurse(tester,frozenset())
    print stable(prob,tester)
    #prefprinter(prob)
    #print prob
    #prefprinter(tester)
    #prefprinter(recurse(tester,frozenset()))
'''


###TEST IF STABLE NOT FOUND


'''
test= []

for i in range(500):
    test.append(generate(3))


for tester in test:
    prob = copy.deepcopy(tester)
    tester = recurse(tester,frozenset())
    #print stable(prob,tester)
    if tester == 'UNSTABLE':
        prefprinter(prob)
    #print prob
    #prefprinter(tester)
    #prefprinter(recurse(tester,frozenset()))
'''
