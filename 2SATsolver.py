class Stack:
    
    def __init__(self):
        self._data = []
        
    def push(self, entry):
        self._data.append(entry)
        
    def top(self):
        return self._data[len(self._data) - 1]
    
    def pop(self):
        top = self.top()
        self._data.pop()
        return top
    
    def isEmpty(self):
        return len(self._data) == 0
    
    def print(self):
        for element in self._data:
            print(element.index(),end=" ")
        print()

class directedVertex:
    
    def __init__(self, i):
        self._index = i
        self._adjacents = []
        self._isOnStack = False
        self._disc = None
        self._low = None
        self._scc = None
        self._truthValue = None
    
    def index(self):
        return self._index
    
    def adjacents(self):
        return self._adjacents
    
    def addAdjacent(self, newAdjacent):
        self._adjacents.append(newAdjacent)
    
    def disc(self):
        return self._disc
    
    def setDisc(self, d):
        self._disc = d
    
    def low(self):
        return self._low
    
    def setLow(self, l):
        self._low = l
    
    def updateLow(self, newValue):
        if newValue < self._low:
            self._low = newValue
    
    def onStack(self, booleanValue):
        self._isOnStack = booleanValue
        
    def isOnStack(self):
        return self._isOnStack
    
    def scc(self):
        return self._scc
    
    def setSCC(self, scc):
        self._scc = scc
        
    def isRoot(self):
        return self._disc == self._low
    
    def truthValue(self):
        return self._truthValue
    
    def setTruthValue(self, truthVal):
        self._truthValue = truthVal
        
    
def Tarjan(vertices):
    
    s = Stack()
    sDFS = Stack()    # DFS stack
    t = 0
    scc = 0
    SCCs = []
        
    for k in range(1, len(vertices)):
        
        if vertices[k].disc() == None:
            sDFS.push(vertices[k])
            s.push(vertices[k])

            vertices[k].setDisc(t)
            vertices[k].setLow(t)
            t += 1
            vertices[k].onStack(True)
            
        else:
            continue
        
        while True:
            if sDFS.isEmpty():
                break
            
            newDFS = False
            for w in sDFS.top().adjacents():
                j = w.index()
                if vertices[j].disc() == None:
                    sDFS.push(vertices[j])
                    s.push(vertices[j])

                    vertices[j].setDisc(t)
                    vertices[j].setLow(t)
                    t += 1
                    vertices[j].onStack(True)
                    
                    newDFS = True
                    break
                    
                elif vertices[j].isOnStack():
                    sDFS.top().updateLow(vertices[j].disc())
                    
            if newDFS:
                continue

            # check if v is the root of current SCC tree
            if sDFS.top().isRoot():
                i = sDFS.top().index()
                j = s.top().index()
                new_SCC = []
                while j != i:
                    j = s.pop().index()
                    vertices[j].onStack(False)
                    vertices[j].setSCC(scc)
                    new_SCC.append(j)
                    j = s.top().index()
                vertices[i].onStack(False)
                vertices[i].setSCC(scc)
                scc += 1
                new_SCC.append(i)
                SCCs.append(new_SCC)
                s.pop()
            j = sDFS.pop().index()
            if not sDFS.isEmpty():
                sDFS.top().updateLow(vertices[j].low())
            
    return SCCs
            
    
def SCC_2SAT(n, clauses):     # n = number of variables 
    
    # construct the implication graph
    # initialize directed vertices for each variable (with index i) and its negation (with index i + number of variables)
    vertices = [directedVertex(i) for i in range(2*n+1)]     # create an empty vertex at index 0
    for c in clauses:
        # if the clause is (xi or not xi), ignore the clause
        if c[0] == -c[1]:
            continue
            
        if c[0] == c[1]:
            if c[0] < 0:
                vertices[-c[0]].addAdjacent(vertices[-c[0]+n])
            
            elif c[0] > 0:
                vertices[c[0]+n].addAdjacent(vertices[c[0]])
            continue
        
        # for each clause (xi OR xj) create two edge (from (not xi) to (xj), from (not xj) to (xi))
        if c[0] < 0 and c[1] < 0:
            vertices[-c[0]].addAdjacent(vertices[-c[1]+n])
            vertices[-c[1]].addAdjacent(vertices[-c[0]+n])
            
        if c[0] < 0 and c[1] > 0:
            vertices[-c[0]].addAdjacent(vertices[c[1]])
            vertices[c[1]+n].addAdjacent(vertices[-c[0]+n])
            
        if c[0] > 0 and c[1] < 0:
            vertices[c[0]+n].addAdjacent(vertices[-c[1]+n])
            vertices[-c[1]].addAdjacent(vertices[c[0]])
            
        if c[0] > 0 and c[1] > 0:
            vertices[c[0]+n].addAdjacent(vertices[c[1]])
            vertices[c[1]+n].addAdjacent(vertices[c[0]])
    
    
    # find SCCs of the implication graph in reverse topological ordering
    SCCs = Tarjan(vertices)
    
    # check satisfiability by checking whether a variable and its negation are included in the same SCC
    for i in range(1, n+1):
        if vertices[i].scc() == vertices[i+n].scc():
            return "UNSATISFIABLE"
        
    # in reverse topological ordering of all SCCs, if the variables in a SCC are not assigned truth values yet,
    # set them all True and all their negations False
    for SCC in SCCs:
        for i in SCC:
            if vertices[i].truthValue() == None:
                vertices[i].setTruthValue(True)
                if i > n:
                    vertices[i-n].setTruthValue(False)
                else:
                    vertices[i+n].setTruthValue(False)
    
    # return the satisfying assignment set
    assignment = []
    for i in range(1, n+1):
        if vertices[i].truthValue():
            assignment.append(i)
        else:
            assignment.append(-i)
    return assignment

n, m = map(int, input().split()[:2])
clauses = []
for i in range(m):
    c = tuple(map(int, input().split()[:2]))
    clauses.append(c)
satisfying_assignment = SCC_2SAT(n, clauses)
if satisfying_assignment == "UNSATISFIABLE":
    print(satisfying_assignment)
else:
    print("SATISFIABLE")
    for i in range(len(satisfying_assignment)):
        print(satisfying_assignment[i], end=" ")
    
