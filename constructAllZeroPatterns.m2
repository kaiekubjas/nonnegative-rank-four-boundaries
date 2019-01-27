restart

------------------------------------------------------------------------------------------------
--construct all partitions of an integer k to r pieces
--such that the first component is at most r-1 (see lemma in the paper)
myPartitions=k->delete(null,for i to #(partitions k)-1 
    list if(#(partitions k)#i==r and (partitions k)#i#0<=r-1) 
    then (partitions k)#i);

------------------------------------------------------------------------------------------------
--functions that check properties on the level of a zero pattern
--this means that knowledge about other zero patterns is not needed

--function that checks if there are too many (more than r-2) zeros per row
tooManyZerosPerRow = zeroPattern->(
    rowPartitions := partition((a,b)->b,zeroPattern);
    rows := keys rowPartitions;
    for row in rows do (
	if(#rowPartitions#row > r-2) then return true;
	);
    return false;
    );

--function that checks if there is a row that consists of zeros
--this is probably not needed because there is a check if more than r-2 zeros per row
rowOfZeros=zeroPattern->(
     for row from 1 to m do (
         myList := for col from 1 to r list (col,row);    
         if(isSubset(myList, zeroPattern)) then return true;
     );
     return false;
);

-- function that checks whether zeros in one column
-- are contained in the zeros of another column
columnContainedInAnotherColumn=zeroPattern->(
    --make list of zeros for each column
    partitionList := partition((a,b)->a,zeroPattern);
    --project these lists to row coordinates
    partitionListProjected := {};
    for col from 1 to r do (
	partitionListProjected = append(partitionListProjected,apply(partitionList#col,(a,b)->b));
    	);
    --return true if a projected column list is subset of another projected column list
    for col1 to r-1 do (
	for col2 to col1-1 do (
	    if(isSubset(partitionListProjected#col1,partitionListProjected#col2)) then return true;
	    );
        for col2 from col1+1 to r-1 do (
	    if(isSubset(partitionListProjected#col1,partitionListProjected#col2)) then return true;
	    );
    	);
    return false;
    );

--check if a zero pattern is an orbit representative
--NB! this check determines some non orbit representatives to be orbit representatives
--however it is useful because it considerably reduces the number of zero patterns
orbitRepresentative=zeroPattern->(
    --partition accordin to columns of A
    colPartitions := partition((a,b)->a,zeroPattern);
    --loop over all columns but the first one
    for i from 2 to r do (
	--take the union of zeros with column less than i
    	smallerZeros := {};
	for j from 1 to i-1 do (
	    smallerZeros = smallerZeros | colPartitions#j;
	    );
	--partition these zeros according to rows
	rowPartitions := partition((a,b)->b,smallerZeros);
	rowKeys := keys(rowPartitions);
	thisColRows := colPartitions#i/((a,b)->b);
	--check for every zero in the current column if it could have been in a smaller row
	for myZero in colPartitions#i do (
	    currentRow := myZero#1;
	    --if in the first row then ok
	    if(currentRow == 1) then continue;
	    --if this row doesn't have zeros and the previous row doesn't have zeros
	    --and there is no zero in the previous row of this column, then not an orbit representative
	    if(not member(currentRow,rowKeys)) then (
		if(not member(currentRow-1,thisColRows) and not member(currentRow-1,rowKeys)) then return false;
		) else (
		--if the zeros in on the the previous rows are the same as in this row and there is no row in this column at this previous row
		--then not an orbit representative
	    	for j from 1 to currentRow-1 do (
		    if not member(j,thisColRows) and ((rowPartitions#(currentRow))/((a,b)->a)) == ((rowPartitions#j)/((a,b)->a)) then return false;
		    );
		);
	    );
	);
    return true;
    );

--check if a zero pattern has full support
fullSupport = (zeroPattern,i) -> (
    rowPartitions := partition((a,b)->b,zeroPattern);
    if(i == 5 or #keys(rowPartitions) == i) then return true;
    return false;
    );

------------------------------------------------------------------------------------------------
--function that construct possible zeros for all columns given a partition
--the output is a list of lists
zerosForColumnsForAPartition = myPartition -> (	
    --construct lists myList_(0),...,myList(r-1) with all possible 
    --zero patterns for columns 0,...,r-1
    --first column contains first possible entries
    myColumnList_(0) = {for j from 1 to myPartition#0 list j};
    --other columns contain all possible entries
    for col from 1 to r-1 do (
	myColumnList_(col) = subsets(Lm,myPartition#col); 
    	);
    --remove subsets that are subset of the first column
    for col from 1 to r-1 do (
	for zeros in myColumnList_(col) do (
	    if(isSubset(zeros,myColumnList_(0)#0)) then myColumnList_(col) = delete(zeros,myColumnList_(col));
	    );
	);
    zerosForColumns = {};
    for col to r-1 do zerosForColumns = append(zerosForColumns,myColumnList_(col));
    return zerosForColumns;
    );

--function that combines zeros for each column to zeros for a matrix
combineZerosForColumns = zerosForColumns -> (
    zeroPatterns := {};
    --the total number of zero patterns that can be obtained from zeros for each column
    i := 1;
    sizeList := {i};
    for col to r-1 do (
	i = i*#(zerosForColumns#(r-1-col));
	sizeList = append(sizeList,i);
     	);
    sizeList = reverse sizeList;
    --construct all zero sets
    --this approach avoids nested loops
    --zerosForCurrentColumn fetches the correct zeros for a column
    for j to i-1 do (
	zeroPattern := {};
    	for col to r-1 do (
	    zerosForCurrentColumn := zerosForColumns#(col)#(floor((j%sizeList#col)/sizeList#(col+1)));
	    for row in zerosForCurrentColumn do (
	    	zeroPattern = append(zeroPattern,(col+1,row));
	    	);
	    );
    	--check properties that can be checked for a zero pattern
    	if(not tooManyZerosPerRow(zeroPattern) and not columnContainedInAnotherColumn(zeroPattern) and orbitRepresentative(zeroPattern)) then zeroPatterns = append(zeroPatterns,zeroPattern);
	);
    return zeroPatterns;	
    );	

--function that constructs zero patterns for a partition
zeroPatternsForAPartition = myPartition -> (
    zerosForColumns := zerosForColumnsForAPartition(myPartition);
    zeroPatterns := combineZerosForColumns(zerosForColumns);
    return zeroPatterns;
    )

------------------------------------------------------------------------------------------------
-- remove column orbits of A

--permuteIndicesA takes a list of pairs of indices and applies column permutation cA and row permutation rA on the indices
permuteZeroPatternsA=(l,cA,rA)->sort(for i to #l-1 list(cA#(l#i#0-1),rA#(l#i#1-1)));

--this functions constructs column 
--permutations of A that permute columns
--with the same number of zeros only
columnPermutationsForAPartition = myPartition -> (
    --myCardinalities partitions according to the number of zeros in a column
    myCardinalities := partition(j->myPartition#(j-1),{1,2,3,4});
    myPermutations := {};
    for j to #myCardinalities-1 do (
	myPermutations = append(myPermutations,permutations (sort values(myCardinalities))#j);
    	);
    permC := myPermutations#0;
    for j from 1 to #myPermutations-1 do (
	permC = toList(set(permC) ** set(myPermutations#j));
        permC = apply(permC,flatten);
	permC = apply(permC,toList);
    	);  
    return permC;
    );

--function that removes column orbits of A
removeColumnOrbits = (zeroPatterns,permC) -> (
    permR := {Lm};
    i := 0;
    while i < #zeroPatterns do (  
    	for j to #permC-1 do (
    	    for k to #permR-1 do (
            	permutedList := sort(permuteZeroPatternsA(zeroPatterns#i,permC#j,permR#k));
	    	if(zeroPatterns#i != permutedList) then zeroPatterns=delete(permutedList,zeroPatterns);      
	    	);
    	    );
	i = i + 1;
    	);
    return zeroPatterns;
    );

------------------------------------------------------------------------------------------------
--remove row and column orbits of A
--permuteIndicesA takes a list of pairs of indices and applies column permutation cA and row permutation rA on the indices

--row permutations that permute only the support (assuming the support is consecutive)
rowPermutationsForAZeroPattern = zeroPattern -> (
    rowPartitions := partition((a,b)->b,zeroPattern);
    rowKeys := keys(rowPartitions);
    rowPermutations := permutations rowKeys; 
    tail := for i from last(rowKeys) + 1 to m list i;
    rowPermutations = rowPermutations / (perm -> join(perm,tail));
    return rowPermutations;
    );

--function that removes row and column orbits of A
removeRowAndColumnOrbitsA = (zeroPatterns,permC) -> (
    i := 0;
    while i < #zeroPatterns do (  
	permR := rowPermutationsForAZeroPattern(zeroPatterns#i);
    	for j to #permC-1 do (
    	    for k to #permR-1 do (
            	permutedList := sort(permuteZeroPatternsA(zeroPatterns#i,permC#j,permR#k));
	    	if(zeroPatterns#i != permutedList) then zeroPatterns=delete(permutedList,zeroPatterns);      
	    	);
    	    );
	i = i + 1;
    	);
    return zeroPatterns;
    );

------------------------------------------------------------------------------------------------
-- remove p_(i,j) that are zero
hasZeroEntry = zeroPattern -> (
    zeroPatternA := zeroPattern#0;
    zeroPatternB := zeroPattern#1;
    rowPartitionA := partition((a,b)->b,zeroPatternA);
    colPartitionB := partition((a,b)->b,zeroPatternB);
    rowPartitionAProjected := {};
    colPartitionBProjected := {};
    for keyA in keys(rowPartitionA) do (
        rowPartitionAProjected = append(rowPartitionAProjected,apply(rowPartitionA#keyA,(a,b)->a));
    	);
    for keyB in keys(colPartitionB) do (
        colPartitionBProjected = append(colPartitionBProjected,apply(colPartitionB#keyB,(a,b)->a));
    	);
    for rowA in rowPartitionAProjected do (
	for colB in colPartitionBProjected do (
	    if(sort(unique(join(rowA,colB))) == Lr) then return true;
	    );
	);
    return false;
    );

------------------------------------------------------------------------------------------------
--function that permutes rows of B
permuteRowsOfB=(zeroPattern,myPermutation)->
    sort(apply(zeroPattern,(a,b)->(myPermutation#(a-1),b)));

--combine zero patterns for A and B
combineZeroPatternsForAB = (zeroPatternsA) -> (
    zeroPatternsAB := {};
    --permutations of rows of B
    permutationsLr := permutations Lr;
    --loop over all partitions of zeros patterns for B
    for i from 4 to 6 do (
	for j to #zeroPatternsA#(n,i)-1 do (
	    --loop over all partitions of zero patterns for A
            for k to #zeroPatternsA#(m,13-i)-1 do (
		print (i,j,k);
		zeroPatternsCurrent := {};
	      	--loop over all zero patterns for B
    	    	for zerosB in zeroPatternsA#(n,i)#j do (
		    --check that n=5 or the zero pattern is over all columns
		    if (not fullSupport(zerosB,n)) then continue;
		    for zerosA in zeroPatternsA#(m,13-i)#k do (
		        --loop over all zero patterns for A
		    	if (not fullSupport(zerosA,m)) then continue;
	    		--we have to consider all possible row permutations for B
	    		for myPermutation in permutationsLr do (
			    currentZeroPattern := {zerosA,permuteRowsOfB(zerosB,myPermutation)};
	            	    if(not hasZeroEntry(currentZeroPattern)) then zeroPatternsCurrent = append(zeroPatternsCurrent,currentZeroPattern);
	    	    	    );
			);
    	    	    );
		zeroPatternsAB = append(zeroPatternsAB,zeroPatternsCurrent);
		);
	    );
	);
    return zeroPatternsAB;
    );


--construct partition of zeros in columns
constructPartition = zeroPattern -> (
    columnPartition := partition((a,b)->a,zeroPattern);
    myPartition := for i in keys(columnPartition) list #columnPartition#i;
    return myPartition;
    );

------------------------------------------------------------------------------------------------
-- use row and column orbits for A and B simultaneously (partial, to speed up computations)

permuteAB=(l1,l2,rA,cArB,cB)->{sort(apply(l1,(x,y)->(cArB#(x-1),rA#(y-1)))),sort(apply(l2,(x,y)->(cArB#(x-1),cB#(y-1))))}

--function that removes row and column orbits
--for A only column permutations are considered
removeRowAndColumnOrbitsAB1 = (zeroPatterns,permrA,permcArB) -> (
    i := 0;
    while i < #zeroPatterns do (  
	permcB := rowPermutationsForAZeroPattern(zeroPatterns#i#1);
       	for j to #permrA-1 do (      
       	    for k to #permcArB-1 do (
	    	for l to #permcB-1 do (
	      	    permutedZeroPattern := permuteAB(zeroPatterns#i#0,zeroPatterns#i#1,permrA#j,permcArB#k,permcB#l);
              	    if(zeroPatterns#i != permutedZeroPattern) then zeroPatterns = delete(permutedZeroPattern,zeroPatterns);
              	    );
       	    	);
    	    );
	i = i + 1;
    	);
    return zeroPatterns;
    );

--function that removes row and column orbits
removeRowAndColumnOrbitsAB2 = (zeroPatterns,permcArB) -> (
    i := 0;
    while i < #zeroPatterns do (  
	permrA := rowPermutationsForAZeroPattern(zeroPatterns#i#0);
	permcB := rowPermutationsForAZeroPattern(zeroPatterns#i#1);
       	for j to #permrA-1 do (      
       	    for k to #permcArB-1 do (
	    	for l to #permcB-1 do (
	      	    permutedZeroPattern := permuteAB(zeroPatterns#i#0,zeroPatterns#i#1,permrA#j,permcArB#k,permcB#l);
              	    if(zeroPatterns#i != permutedZeroPattern) then zeroPatterns = delete(permutedZeroPattern,zeroPatterns);
              	    );
       	    	);
    	    );
	i = i + 1;
    	);
    return zeroPatterns;
    );

------------------------------------------------------------------------------------------------
--once a zero pattern has been constructed, check that it has the correct dimension
correctDimension = zeroPattern -> (
    R=QQ[a_(1,1)..a_(r,m),b_(1,1)..b_(r,n)];
    A=for i from 1 to r list for j from 1 to m list a_(i,j);
    M1=mutableMatrix A;
    ZerosA=zeroPattern#0;
    for i to #ZerosA-1 do M1_((ZerosA#i#0-1,ZerosA#i#1-1))=0;
    M1=matrix M1;
    --construct matrix B
    B=for i from 1 to r list for j from 1 to n list b_(i,j);
    M2=mutableMatrix B;
    ZerosB=zeroPattern#1;
    for i to #ZerosB-1 do M2_((ZerosB#i#0-1,ZerosB#i#1-1))=0;
    M2=matrix M2;
    M=transpose(M1)*M2; -- p's as polynomials in a's and b's
    --compute the dimension
    N=matrix{flatten entries M}; -- write entries of M as a 1x16 matrix
    J=jacobian N;   
    L1=for i from 1 to r list for j from 1 to m list a_(i,j)=>random(1,200);
    L2=for i from 1 to r list for j from 1 to n list b_(i,j)=>random(1,200);
    L=join(flatten L1, flatten L2);
    C=sub(J,L);
    if(rank(C)==m*r+n*r-r^2-1) then return true;
    return false;
    )

------------------------------------------------------------------------------------------------
--printing in the MATLAB code format
printInMATLABFormat = zeroPattern -> (
    for i to #zeroPattern#0-1 do (
    	<< "U(" << zeroPattern#0#i#1 <<"," << zeroPattern#0#i#0 << ")=0; ";
    	);
    for i to #zeroPattern#1-1 do (
    	<< "V(" << zeroPattern#1#i#0 <<"," << zeroPattern#1#i#1 << ")=0; "
    	);
    << "\n";
    );

--printing in the MATLAB code format 2
printInMATLABFormat2 = zeroPatterns -> (
    << "zeroPatterns = [\n";
    for zeroPattern in zeroPatterns do (
	<< "'";
    for i to #zeroPattern#0-1 do (
    	<< "U(" << zeroPattern#0#i#1 <<"," << zeroPattern#0#i#0 << ")=0; ";
    	);
    for i to #zeroPattern#1-1 do (
    	<< "V(" << zeroPattern#1#i#0 <<"," << zeroPattern#1#i#1 << ")=0; "
    	);
    << "';\n";
    );
    << "];";
    );

------------------------------------------------------------------------------------------------
--print a zero-pattern
printZeroPattern = zeroPattern -> (
    A=for i from 1 to r list for j from 1 to m list 1;
    B=for i from 1 to r list for j from 1 to n list 1;
    M1=mutableMatrix A;
    ZerosA=zeroPattern#0;
    for i to #ZerosA-1 do M1_((ZerosA#i#0-1,ZerosA#i#1-1))=0;
    M1=transpose(M1);
    --construct matrix B
    M2=mutableMatrix B;
    ZerosB=zeroPattern#1;
    for i to #ZerosB-1 do M2_((ZerosB#i#0-1,ZerosB#i#1-1))=0;
    print(M1,M2);
    );

------------------------------------------------------------------------------------------------
--main part
--construct all possible zero patterns for the matrix A
--k is the number of zeros in the matrix A
r=4;
Lr = for i from 1 to r list i;

--zero patterns are nested according to number of zeros and then partition into columns
zeroPatternsA = {};
for m from 5 to 9 do (
    Lm = for i from 1 to m list i;
    for k from 4 to 9 do (
    	print (m,k);
    	zeroPatternsFixedNumber = {};
    	P = myPartitions(k);
    	for i to #P-1 do (
    	    zerosA_(i) = zeroPatternsForAPartition(P#i);
    	    permC = columnPermutationsForAPartition(P#i);
    	    zerosA2_(i) = removeColumnOrbits(zerosA_(i),permC);
    	    zerosA3_(i) = removeRowAndColumnOrbitsA(zerosA2_(i),permC);
    	    if(#zerosA_(i)>0) then zeroPatternsFixedNumber = append(zeroPatternsFixedNumber,zerosA3_(i));
    	    );
    	zeroPatternsA = append(zeroPatternsA,zeroPatternsFixedNumber);
    	);
    );

myList = flatten for m from 5 to 9 list 
    for k from 4 to 9 list 
    	(m,k) => zeroPatternsA#((m-5)*6+(k-4));
       
zeroPatternsAHashTable = hashTable myList;

--run from here if have loaded the hashtable from below
--for every matrix size the following part of the code has to be run separately
m=9;
n=5;

Lm = for i from 1 to m list i;
Ln = for i from 1 to n list i;

zeroPatternsAB = {};
zeroPatternsAB = combineZeroPatternsForAB(zeroPatternsAHashTable);
zeroPatternsAB = delete({},zeroPatternsAB);
# flatten zeroPatternsAB
#zeroPatternsAB
for i to #zeroPatternsAB-1 do (
    print i;
    myPartition = constructPartition(zeroPatternsAB#i#0#0);
    permcArB = columnPermutationsForAPartition(myPartition);
    zerosAB_(i) = removeRowAndColumnOrbitsAB1(zeroPatternsAB#i,{Lm},permcArB);
    zerosAB2_(i) = removeRowAndColumnOrbitsAB2(zerosAB_(i),permcArB);
    );

zeroPatternsAB2 = {};
for i to #zeroPatternsAB-1 do (
    zeroPatternsAB2 = join(zeroPatternsAB2,zerosAB2_(i));
    )

#zeroPatternsAB2
toString zeroPatternsAB2

--check that they have correct dimension
for zeroPattern in zeroPatternsAB2 do (
    print correctDimension(zeroPattern);
    );

for zeroPattern in zeroPatternsAB2 do (
    printInMATLABFormat(zeroPattern);
    );

printInMATLABFormat2(zeroPatternsAB2);

------------------------------------------------------------------------------------------------
-- hash table where key is (m,k)
-- m is the number of rows of A
-- k is the number of zeros

new HashTable from {(5,4) => {{{(1,1), (2,2), (3,3), (4,4)}}}, (6,4) => {{{(1,1), (2,2), (3,3), (4,4)}}}, (5,5) => {{{(1,1), (1,2), (2,3), (3,4), (4,5)}}}, (6,5) =>
       {{{(1,1), (1,2), (2,3), (3,4), (4,5)}}}, (5,6) => {{{(1,1), (1,2), (2,1), (2,3), (3,4), (4,5)}}}, (7,4) => {{{(1,1), (2,2), (3,3), (4,4)}}}, (6,6) => {{{(1,1), (1,2),
       (1,3), (2,4), (3,5), (4,6)}}, {{(1,1), (1,2), (2,1), (2,3), (3,4), (4,5)}, {(1,1), (1,2), (2,3), (2,4), (3,5), (4,6)}}}, (5,7) => {{{(1,1), (1,2), (2,1), (2,3), (3,2),
       (3,3), (4,4)}, {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,5)}}}, (7,5) => {{{(1,1), (1,2), (2,3), (3,4), (4,5)}}}, (8,4) => {{{(1,1), (2,2), (3,3), (4,4)}}}, (9,4) =>
       {{{(1,1), (2,2), (3,3), (4,4)}}}, (6,7) => {{{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (4,6)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,3), (4,4)}, {(1,1), (1,2), (2,1),
       (2,3), (3,2), (3,4), (4,5)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6)}}}, (5,8) => {{{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,5)}}, {{(1,1), (1,2),
       (2,1), (2,3), (3,2), (3,3), (4,4), (4,5)}, {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,3), (4,4)}, {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,3), (4,5)}}}, (7,6) =>
       {{{(1,1), (1,2), (1,3), (2,4), (3,5), (4,6)}}, {{(1,1), (1,2), (2,1), (2,3), (3,4), (4,5)}, {(1,1), (1,2), (2,3), (2,4), (3,5), (4,6)}}}, (8,5) => {{{(1,1), (1,2), (2,3),
       (3,4), (4,5)}}}, (9,5) => {{{(1,1), (1,2), (2,3), (3,4), (4,5)}}}, (6,8) => {{{(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,5), (4,6)}}, {{(1,1), (1,2), (1,3), (2,1),
       (2,4), (3,2), (3,4), (4,5)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,4), (3,5), (4,6)}}, {{(1,1), (1,2), (2,1),
       (2,3), (3,2), (3,3), (4,4), (4,5)}, {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,3), (4,4)}, {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,3), (4,5)}, {(1,1), (1,2),
       (2,1), (2,3), (3,2), (3,4), (4,5), (4,6)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,4), (4,6)}}}, (5,9) => {{{(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,3), (3,4),
       (4,5)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,3), (4,5)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,4), (4,5)}}}, (7,7) => {{{(1,1), (1,2),
       (1,3), (2,1), (2,4), (3,5), (4,6)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (4,7)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,3), (4,4)}, {(1,1), (1,2), (2,1), (2,3),
       (3,2), (3,4), (4,5)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6)}, {(1,1), (1,2), (2,3), (2,4), (3,5), (3,6), (4,7)}}}, (8,6) => {{{(1,1), (1,2), (1,3), (2,4),
       (3,5), (4,6)}}, {{(1,1), (1,2), (2,1), (2,3), (3,4), (4,5)}, {(1,1), (1,2), (2,3), (2,4), (3,5), (4,6)}}}, (9,6) => {{{(1,1), (1,2), (1,3), (2,4), (3,5), (4,6)}}, {{(1,1),
       (1,2), (2,1), (2,3), (3,4), (4,5)}, {(1,1), (1,2), (2,3), (2,4), (3,5), (4,6)}}}, (6,9) => {{{(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,3), (3,4), (4,5)}, {(1,1),
       (1,2), (1,3), (2,1), (2,2), (2,4), (3,3), (3,5), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,2), (3,4), (4,6)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2),
       (3,4), (4,3), (4,5)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,5), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,4), (4,5)}, {(1,1), (1,2),
       (1,3), (2,1), (2,4), (3,2), (3,5), (4,3), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,4), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,4), (3,5), (4,5),
       (4,6)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6), (4,5), (4,6)}}}, (7,8) => {{{(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,5), (4,6)}, {(1,1), (1,2), (1,3),
       (2,1), (2,4), (2,5), (3,6), (4,7)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,5)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,6)}, {(1,1), (1,2),
       (1,3), (2,1), (2,4), (3,4), (3,5), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (3,6), (4,7)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6), (4,7)}}, {{(1,1),
       (1,2), (2,1), (2,3), (3,2), (3,3), (4,4), (4,5)}, {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,3), (4,4)}, {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,3), (4,5)},
       {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,5), (4,6)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,4), (4,6)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6),
       (4,7)}}}, (8,7) => {{{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (4,6)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (4,7)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,3),
       (4,4)}, {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,5)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6)}, {(1,1), (1,2), (2,3), (2,4), (3,5), (3,6), (4,7)}}}, (9,7) =>
       {{{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (4,6)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (4,7)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,3), (4,4)}, {(1,1), (1,2),
       (2,1), (2,3), (3,2), (3,4), (4,5)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6)}, {(1,1), (1,2), (2,3), (2,4), (3,5), (3,6), (4,7)}}}, (7,9) => {{{(1,1), (1,2),
       (1,3), (2,1), (2,2), (2,4), (3,3), (3,4), (4,5)}, {(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,3), (3,5), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,5), (3,6),
       (4,7)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,2), (3,4), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,2), (3,6), (4,7)}, {(1,1), (1,2), (1,3), (2,4),
       (2,5), (2,6), (3,1), (3,4), (4,7)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,3), (4,5)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,5), (4,6)},
       {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,4), (4,5)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,3), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4),
       (3,2), (3,5), (4,4), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,6), (4,7)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,4), (3,5), (4,5), (4,6)}, {(1,1),
       (1,2), (1,3), (2,1), (2,4), (3,4), (3,5), (4,6), (4,7)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (3,6), (4,5), (4,7)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6),
       (4,5), (4,6)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6), (4,5), (4,7)}}}, (8,8) => {{{(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,5), (4,6)}, {(1,1), (1,2),
       (1,3), (2,1), (2,4), (2,5), (3,6), (4,7)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (2,6), (3,7), (4,8)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,5)}, {(1,1),
       (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,4), (3,5), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (3,6), (4,7)},
       {(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6), (4,7)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (3,7), (4,8)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,3), (4,4),
       (4,5)}, {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,3), (4,4)}, {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,3), (4,5)}, {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4),
       (4,5), (4,6)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,4), (4,6)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6), (4,7)}, {(1,1), (1,2), (2,3), (2,4), (3,5),
       (3,6), (4,7), (4,8)}}}, (9,8) => {{{(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,5), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,6), (4,7)}, {(1,1), (1,2),
       (1,3), (2,4), (2,5), (2,6), (3,7), (4,8)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,5)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,6)}, {(1,1),
       (1,2), (1,3), (2,1), (2,4), (3,4), (3,5), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (3,6), (4,7)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6), (4,7)},
       {(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (3,7), (4,8)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,3), (4,4), (4,5)}, {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,3),
       (4,4)}, {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,3), (4,5)}, {(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,5), (4,6)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (3,5),
       (4,4), (4,6)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6), (4,7)}, {(1,1), (1,2), (2,3), (2,4), (3,5), (3,6), (4,7), (4,8)}}}, (8,9) => {{{(1,1), (1,2), (1,3),
       (2,1), (2,2), (2,4), (3,3), (3,4), (4,5)}, {(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,3), (3,5), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,5), (3,6),
       (4,7)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,2), (3,4), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,2), (3,6), (4,7)}, {(1,1), (1,2), (1,3), (2,1),
       (2,4), (2,5), (3,6), (3,7), (4,8)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (2,6), (3,1), (3,4), (4,7)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (2,6), (3,1), (3,7), (4,8)}},
       {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,3), (4,5)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,5), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4),
       (3,2), (3,5), (4,4), (4,5)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,3), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,4), (4,6)}, {(1,1),
       (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,6), (4,7)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,4), (3,5), (4,5), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,4), (3,5),
       (4,6), (4,7)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (3,6), (4,5), (4,7)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (3,6), (4,7), (4,8)}, {(1,1), (1,2), (1,3),
       (2,4), (2,5), (3,4), (3,6), (4,5), (4,6)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6), (4,5), (4,7)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6), (4,7),
       (4,8)}}}, (9,9) => {{{(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,3), (3,4), (4,5)}, {(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,3), (3,5), (4,6)}, {(1,1), (1,2),
       (1,3), (2,1), (2,2), (2,4), (3,5), (3,6), (4,7)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,2), (3,4), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,2), (3,6),
       (4,7)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,6), (3,7), (4,8)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (2,6), (3,1), (3,4), (4,7)}, {(1,1), (1,2), (1,3), (2,4),
       (2,5), (2,6), (3,1), (3,7), (4,8)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (2,6), (3,7), (3,8), (4,9)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,3), (4,5)},
       {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,5), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,4), (4,5)}, {(1,1), (1,2), (1,3), (2,1), (2,4),
       (3,2), (3,5), (4,3), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,4), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,6), (4,7)}, {(1,1),
       (1,2), (1,3), (2,1), (2,4), (3,4), (3,5), (4,5), (4,6)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,4), (3,5), (4,6), (4,7)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (3,6),
       (4,5), (4,7)}, {(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (3,6), (4,7), (4,8)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6), (4,5), (4,6)}, {(1,1), (1,2), (1,3),
       (2,4), (2,5), (3,4), (3,6), (4,5), (4,7)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6), (4,7), (4,8)}, {(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (3,7), (4,8),
       (4,9)}}}}

------------------------------------------------------------------------------------------------
--these are the zero patterns for different sizes of matrices constructed using this code

--5x5
zeroPatternsAB = {{{(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,3), (3,4), (4,5)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,3), (4,5)}, {(1,1),
      (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,4), (4,5)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4),
      (4,5)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,5)}, {(1,3), (2,1), (2,2), (3,4), (4,5)}}, {{(1,1), (1,2), (1,3), (2,1),
      (2,4), (3,2), (3,4), (4,5)}, {(1,3), (2,4), (3,5), (4,1), (4,2)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,3), (4,4), (4,5)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}}, {{(1,1),
      (1,2), (2,1), (2,3), (3,2), (3,3), (4,4), (4,5)}, {(1,3), (2,4), (3,5), (4,1), (4,2)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,3), (4,4)}, {(1,1), (1,2), (2,3),
      (3,4), (4,5)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,3), (4,5)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,3), (4,5)},
      {(1,3), (2,4), (3,1), (3,2), (4,5)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,3), (4,4)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2),
      (3,4), (4,5)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,5)}, {(1,1), (1,2), (2,4), (3,5), (4,1), (4,3)}}, {{(1,1), (1,2),
      (2,1), (2,3), (3,2), (3,4), (4,5)}, {(1,4), (2,1), (2,2), (3,1), (3,3), (4,5)}}}

--6x5
zeroPatternsAB = {{{(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,3), (3,5), (4,6)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,2), (3,4), (4,6)}, {(1,1),
       (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,4), (4,5), (4,6)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5),
       (4,3), (4,6)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,4), (4,6)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3),
       (2,1), (2,4), (3,4), (3,5), (4,5), (4,6)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6), (4,5), (4,6)}, {(1,1), (2,2), (3,3), (4,4)}},
       {{(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,5), (4,6)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,5), (4,6)}, {(1,3), (2,4),
       (3,1), (3,2), (4,5)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,6)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5),
       (4,6)}, {(1,3), (2,1), (2,2), (3,4), (4,5)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5), (4,6)}, {(1,3), (2,4), (3,5), (4,1), (4,2)}}, {{(1,1), (1,2), (1,3),
       (2,1), (2,4), (3,4), (3,5), (4,6)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,4), (3,5), (4,6)}, {(1,3), (2,1), (2,2), (3,4), (4,5)}},
       {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,4), (3,5), (4,6)}, {(1,3), (2,4), (3,1), (3,2), (4,5)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,4), (3,5), (4,6)}, {(1,3), (2,4),
       (3,5), (4,1), (4,2)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,5), (4,6)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,5),
       (4,6)}, {(1,3), (2,1), (2,2), (3,4), (4,5)}}, {{(1,1), (1,2), (2,1), (2,3), (3,2), (3,4), (4,5), (4,6)}, {(1,3), (2,4), (3,5), (4,1), (4,2)}}, {{(1,1), (1,2), (2,1),
       (2,3), (3,4), (3,5), (4,4), (4,6)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (4,6)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (4,5)}},
       {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (4,6)}, {(1,1), (1,2), (2,4), (3,1), (3,3), (4,5)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (4,6)}, {(1,4), (2,1), (2,2),
       (3,1), (3,3), (4,5)}}, {{(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6)},
       {(1,1), (1,2), (2,4), (3,1), (3,3), (4,5)}}, {{(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6)}, {(1,1), (1,2), (2,4), (3,5), (4,1), (4,3)}}}

--6x6
zeroPatternsAB = {{{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (4,6)}, {(1,1), (1,2), (1,3), (2,4), (3,5), (4,6)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (4,6)}, {(1,4), (2,1), (2,2),
       (2,3), (3,5), (4,6)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (4,6)}, {(1,4), (2,5), (3,1), (3,2), (3,3), (4,6)}}, {{(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6)},
       {(1,1), (1,2), (1,3), (2,4), (3,5), (4,6)}}, {{(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6)}, {(1,4), (2,5), (3,1), (3,2), (3,3), (4,6)}}, {{(1,1), (1,2), (2,1), (2,3),
       (3,4), (3,5), (4,6)}, {(1,4), (2,5), (3,6), (4,1), (4,2), (4,3)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (4,6)}, {(1,1), (1,2), (2,3), (2,4), (3,5), (4,6)}},
       {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (4,6)}, {(1,1), (1,2), (2,5), (3,3), (3,4), (4,6)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (4,6)}, {(1,5), (2,1), (2,2),
       (3,3), (3,4), (4,6)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (4,6)}, {(1,5), (2,6), (3,1), (3,2), (4,3), (4,4)}}, {{(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6)},
       {(1,1), (1,2), (2,3), (2,4), (3,5), (4,6)}}, {{(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6)}, {(1,1), (1,2), (2,5), (3,3), (3,4), (4,6)}}, {{(1,1), (1,2), (2,1), (2,3),
       (3,4), (3,5), (4,6)}, {(1,1), (1,2), (2,5), (3,6), (4,3), (4,4)}}, {{(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6)}, {(1,5), (2,6), (3,1), (3,2), (4,3), (4,4)}}}

--7x5
zeroPatternsAB = {{{(1,1), (1,2), (1,3), (2,1), (2,2), (2,4), (3,5), (3,6), (4,7)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,2), (3,6), (4,7)}, {(1,1),
       (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (2,6), (3,1), (3,4), (4,7)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,2), (3,5),
       (4,6), (4,7)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,4), (3,5), (4,6), (4,7)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3),
       (2,1), (2,4), (3,5), (3,6), (4,5), (4,7)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6), (4,5), (4,7)}, {(1,1), (2,2), (3,3), (4,4)}},
       {{(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,6), (4,7)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,6), (4,7)}, {(1,3), (2,4),
       (3,1), (3,2), (4,5)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (3,6), (4,7)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (3,6),
       (4,7)}, {(1,3), (2,1), (2,2), (3,4), (4,5)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (3,6), (4,7)}, {(1,3), (2,4), (3,1), (3,2), (4,5)}}, {{(1,1), (1,2), (1,3),
       (2,1), (2,4), (3,5), (3,6), (4,7)}, {(1,3), (2,4), (3,5), (4,1), (4,2)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6), (4,7)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}},
       {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6), (4,7)}, {(1,3), (2,1), (2,2), (3,4), (4,5)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6), (4,7)}, {(1,3), (2,4),
       (3,5), (4,1), (4,2)}}, {{(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6), (4,7)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (2,1), (2,3), (3,4), (3,5), (4,6),
       (4,7)}, {(1,3), (2,4), (3,1), (3,2), (4,5)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (4,7)}, {(1,1), (1,2), (2,1), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (1,3),
       (2,4), (2,5), (3,6), (4,7)}, {(1,1), (1,2), (2,4), (3,1), (3,3), (4,5)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (4,7)}, {(1,4), (2,1), (2,2), (3,1), (3,3), (4,5)}},
       {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (4,7)}, {(1,4), (2,5), (3,1), (3,2), (4,1), (4,3)}}, {{(1,1), (1,2), (2,3), (2,4), (3,5), (3,6), (4,7)}, {(1,1), (1,2), (2,1),
       (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (2,3), (2,4), (3,5), (3,6), (4,7)}, {(1,1), (1,2), (2,4), (3,5), (4,1), (4,3)}}}


--7x6
zeroPatternsAB = {{{(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (4,7)}, {(1,1), (1,2), (1,3), (2,4), (3,5), (4,6)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (4,7)}, {(1,4), (2,1), (2,2),
       (2,3), (3,5), (4,6)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (4,7)}, {(1,4), (2,5), (3,1), (3,2), (3,3), (4,6)}}, {{(1,1), (1,2), (2,3), (2,4), (3,5), (3,6), (4,7)},
       {(1,1), (1,2), (1,3), (2,4), (3,5), (4,6)}}, {{(1,1), (1,2), (2,3), (2,4), (3,5), (3,6), (4,7)}, {(1,4), (2,5), (3,6), (4,1), (4,2), (4,3)}}, {{(1,1), (1,2), (1,3), (2,4),
       (2,5), (3,6), (4,7)}, {(1,1), (1,2), (2,3), (2,4), (3,5), (4,6)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (4,7)}, {(1,1), (1,2), (2,5), (3,3), (3,4), (4,6)}},
       {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (4,7)}, {(1,5), (2,1), (2,2), (3,3), (3,4), (4,6)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (4,7)}, {(1,5), (2,6), (3,1),
       (3,2), (4,3), (4,4)}}, {{(1,1), (1,2), (2,3), (2,4), (3,5), (3,6), (4,7)}, {(1,1), (1,2), (2,3), (2,4), (3,5), (4,6)}}, {{(1,1), (1,2), (2,3), (2,4), (3,5), (3,6), (4,7)},
       {(1,1), (1,2), (2,5), (3,6), (4,3), (4,4)}}}


--8x5
zeroPatternsAB =  {{{(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,6), (3,7), (4,8)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (2,6), (3,1), (3,7), (4,8)}, {(1,1),
       (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,1), (2,4), (3,5), (3,6), (4,7), (4,8)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,4), (3,6),
       (4,7), (4,8)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (2,6), (3,7), (4,8)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}}, {{(1,1), (1,2), (1,3),
       (2,4), (2,5), (2,6), (3,7), (4,8)}, {(1,3), (2,4), (3,1), (3,2), (4,5)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (3,7), (4,8)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}},
       {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (3,7), (4,8)}, {(1,3), (2,1), (2,2), (3,4), (4,5)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (3,7), (4,8)}, {(1,3), (2,4),
       (3,5), (4,1), (4,2)}}, {{(1,1), (1,2), (2,3), (2,4), (3,5), (3,6), (4,7), (4,8)}, {(1,1), (1,2), (2,3), (3,4), (4,5)}}}


--9x5
zeroPatternsAB =  {{{(1,1), (1,2), (1,3), (2,4), (2,5), (2,6), (3,7), (3,8), (4,9)}, {(1,1), (2,2), (3,3), (4,4)}}, {{(1,1), (1,2), (1,3), (2,4), (2,5), (3,6), (3,7), (4,8), (4,9)}, {(1,1),
       (2,2), (3,3), (4,4)}}}

