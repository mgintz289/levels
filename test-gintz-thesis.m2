restart
needsPackage("NautyGraphs")
needsPackage("SimplicialDecomposability")
needsPackage("ThickSubcategories")
needsPackage("Complexes")
n=6;
Q=QQ[x_1..x_n];
f = new List;
for i from 1 to n-1 do (
        f=append(f,x_i*x_(i+1));
);
f=append(f,x_1*x_n);
print "We first calculate CSVs of edge ideals of (4n+2)-cycles.\n"
print "CSV of edge ideal of 6-cycle:"
print equigeneratedMonomialCSV(f);
n=10;
Q=QQ[x_1..x_n];
f = new List;
for i from 1 to n-1 do (
        f=append(f,x_i*x_(i+1));
);
f=append(f,x_1*x_n);
print "\nCSV of edge ideal of 10-cycle:"
print equigeneratedMonomialCSV(f);
n=14;
Q=QQ[x_1..x_n];
f = new List;
for i from 1 to n-1 do (
        f=append(f,x_i*x_(i+1));
);
f=append(f,x_1*x_n);
print "\nCSV of edge ideal of 14-cycle:"
print equigeneratedMonomialCSV(f);
print "\nWe now calculate all CSVs of monomial ideals with 6 generators.\n\nWe sort into GCD graphs.\n"
n=6;
allGraphs = apply(generateGraphs(n, OnlyConnected => true),i->graph stringToGraph i);
myGraphs = new List;
for G in allGraphs do (
    badGraph = 0;
    for i from 0 to n-1 do (
        --searching for vertices connected to every other vertex
        if (#(G#i)==(n-1)) then (
            badGraph = 1;
            break;
        );
        --searching for edges connected to each vertex exactly once
        --this may be subsumed by the logic found by using denseEdges elsewhere
        for j in select(G#i,k->(k>i)) do (
            goodVertex = 0;
            for k from 0 to n-1 do (
                if (#intersect(set{i,j},set G#k)!=1 and k!=i and k!=j) then (
                    goodVertex = 1;
                    break;
                );
            );
            if (goodVertex == 0) then (
                badGraph = 1;
                break;
            );
        );
        if (badGraph == 1) then break;
    );
    if (badGraph == 0) then (
        myGraphs = append(myGraphs,G);
    );
);
print concatenate("We have ",toString (#myGraphs)," GCD graphs which may yield non-full CSVs, which we enumerate henceforth and give by their adjacency hashes.\n");
allCSVs = new List;
for graphCount from 0 to (#myGraphs-1) do (
    G = myGraphs#graphCount;
    print concatenate("Graph ",toString (graphCount+1),":");
    print G;
    print "";
    myCliques = apply(allFaces cliqueComplex graph G,i->apply(support(i),j->index j));
    twoCliques = select(apply(allFaces cliqueComplex graph G,i->set apply(support(i),j->index j)),i->(#i==2));  
    --edges whose vertices together touch each vertex; used for finding isolated vertices
    denseEdges = new List;
    for i in myCliques do (
        if #i==2 then (
            if #(toList (set G#(i#0)+ set G#(i#1)))==#G then (
                denseEdges=append(denseEdges,set i);
            );
        );
    );
    --removing edges which imply isolated vertices
    --this trick only works for n=6,
    --2.31 FIX
    if n==6 then (
        for i in denseEdges do (
            for j in denseEdges do (
                for k in twoCliques do (
                    if (#(i + j)==3
                        and (not i==j) and (not i==k) and (not j==k)
                        and #(i + j + k) == 5) then (
                        s = toList ((i+j)-(i*j));
                        if not (set G#(s#0))#?(s#1) then (
                            for l in myCliques do (
                                if set l == k then (
                                    myCliques = delete(l,myCliques);
                                    break;
                                );
                            );
                        );
                    );
                );
            );
            --2.30 FIX
            mySet = set (G#((toList i)#0)) * set (G#((toList i)#1));
            for l in myCliques do (
                if isSubset(mySet,set l) and i * set l == set {} then (
                    myCliques = delete(l,myCliques);
                );
            );
        );
    );
    --finding cliques which cover certain edges, used for confirming that we have the correct GCD graph
    myParents = new MutableHashTable;
    for i in twoCliques do (
        myParents#i=select(toList(0..#myCliques-1),j-> (#i <= #myCliques#j) and isSubset(i,myCliques#j));
    );
    myMatrix=QQ ** matrix apply(toList(0..n-1),i->apply(#myCliques,j->if (set myCliques#j)#?i then 1 else 0));
    myVector = image (QQ ** matrix toList(n:{1}));
    myPreimage = gens preimage(myMatrix,myVector);
    myPreimageV = myPreimage | 0-myPreimage;
    C = coneFromVData(myPreimageV); --linear combinations with shared implied degree at each vertex (so that if the linear combination corresponds to an ideal it is equigenerated)
    C = intersect(C,coneFromVData(id_(QQ^(numRows myPreimageV)))); --imposing positivity conditions
    R = rays C;
    RHelpful = entries transpose R;
    RAll = new MutableHashTable from {toList (#(RHelpful#0):0) => {}};

    --collections of cliques which must have full support, since they cover the intersection of the neighborhoods of the vertices of but are disjoint from an edge in denseEdges (so the edge in question corresponds to an isolated vertex)
    --2.30
    forbiddenSubsets = new List;
    for i in denseEdges do (
        mySet = set (G#((toList i)#0)) * set (G#((toList i)#1));
        for j from 2 to min(#mySet,#myCliques) do (
            for k in subsets(#myCliques,j) do (
                mySmallSet = set select(n,l->(
                    member(l,set flatten join(apply(k,m->myCliques#m)))
                ));
                if isSubset(mySet,mySmallSet) and i * mySmallSet == set {} then (
                    forbiddenSubsets = append(forbiddenSubsets,k);
                );  
            );
        );
    );
    --collecting sets of cliques which do not contain forbidden subsets
    for i from 0 to #RHelpful-1 do (
        for j in keys RAll do (
            myBits = apply(RHelpful#i, j, (a,b) -> min(max(a,b),1));
            lose = false;
            for k in forbiddenSubsets do (
                win = false;
                for l in k do (
                    if myBits#l==0 then win;
                );
                if not win then lose = true;
            );
            if not RAll#?myBits and not lose then RAll#myBits=append(RAll#j,i);
        );
    );
    Q = QQ[b_0..b_(#myCliques-1)];
    myIdeals = new List;   
    --collect our ideals
    for i in keys RAll do (
        if (#(RAll#i)>0) then (
            X = sum apply(#(RAll#i),j->RHelpful#(RAll#i#j));
            f = new MutableList from toList(n:1_Q);
            for j from 0 to #X-1 do (
                for k in myCliques#j do (
                    f#k = f#k * b_j^(X#j);
                );
            );
            f = toList f;
            --filter for those satisfying our GCD graph
            bigloss = 0;
            for i in twoCliques do (
                win = 0;
                for j in myParents#i do (
                    if X#j>0 then (
                        win = 1;
                        break;
                    );
                );
                if win == 0 then (
                    bigloss = 1;
                    break;
                );
            );
            if bigloss == 0 and (numColumns mingens ideal f == #f) then ( --also checking for minimality
                myIdeals = append(myIdeals,f);
            );
        );
    );
    print concatenate("We need to consider ",toString (#myIdeals)," ideals.");
    myCounter = 0;
    for f in myIdeals do (
        fAnswer = equigeneratedMonomialCSV(f);
        isUnique=1;
        for i in allCSVs do (
                myMap = map(ring i,ring fAnswer,vars ring i);
                fAnswer = myMap fAnswer;
            if (fAnswer==i) then (
                isUnique=0;
                break;
            );
        );
        if isUnique==1 then allCSVs = append(allCSVs,fAnswer);
        myCounter = myCounter + 1;
        print concatenate ("\nIdeal ",toString myCounter," of ",toString (#myIdeals),": ",toString f,"\nCSV of this ideal: ",toString fAnswer);
    );
    if graphCount<#myGraphs-1 then print "";
);
print concatenate("We found ",toString (#allCSVs)," CSVs, possibly including the full CSV:");
for i in allCSVs do (
    print "";
    print i;
);
print "\nThese CSVs, up to order, and possibly ignoring the full CSV, are all possible CSVs of monomial ideals with 6 generators."
exit 0;
