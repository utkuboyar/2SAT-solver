class Stack:
    
    def __init__(self):
        self.data = []
        
    def push(self, entry):
        self.data.append(entry)
        
    def top(self):
        return self.data[len(self.data) - 1]
    
    def pop(self):
        top = self.top()
        self.data.pop()
        return top
    
    def isEmpty(self):
        return len(self.data) == 0

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
    t = 0
    scc = 0
    SCCs = []
    
    def DFS(v):
        
        nonlocal s
        nonlocal t
        nonlocal scc
        nonlocal SCCs

        v.setDisc(t)
        v.setLow(t)
        t += 1

        s.push(v)
        v.onStack(True)

        for w in v.adjacents():

            if w.disc() == None:
                DFS(vertices[w.index()])
                v.updateLow(w.low())

            elif w.isOnStack():
                v.updateLow(w.disc())

        # check if v is the root of current SCC tree
        if v.isRoot():
            w = s.pop()
            w.onStack(False)
            w.setSCC(scc)
            new_SCC = [w.index()]
            while w != v:
                w = s.pop()
                w.onStack(False)
                w.setSCC(scc)
                new_SCC.append(w.index())
            scc += 1
            SCCs.append(new_SCC)
            
            
    for vertex in vertices:
            
        if vertex.index() == 0:
            continue
        if vertex.disc() == None:
            DFS(vertices[vertex.index()])
            
    print(SCCs)
    for vertex in vertices:
        print("vertex {} :: onStack: {}, low: {}, disc: {}, scc: {}".format(vertex._index, vertex._isOnStack, vertex._low, vertex._disc, vertex._scc))
    
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
    
