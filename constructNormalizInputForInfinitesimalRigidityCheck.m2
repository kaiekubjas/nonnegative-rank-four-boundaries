restart

constructDualMats=A->(
    V := {};
    r := numcols A;
    K := ring A;
    for i from 0 to numrows A - 1 do (
	for j from 0 to r-1 do (
	    if A_(i,j) == 0 then (
		vmat := map(K^r,K^j,0) | transpose A^{i} | map(K^r,K^(r-j-1),0);
		V = append(V,vmat);
		);
	    );
	);
    V
    )

constructDualVectors=(A,B)->(
    AList := apply(constructDualMats(A), flatten @@ entries);
    BList := apply(constructDualMats(transpose (-1*B)), flatten @@ entries @@ transpose);
    AList | BList
    )
    
makeNormalizFile=(M,outFile) -> (
    outFile << "amb_space " << numcols M << endl;
    outFile << "cone " << numrows M << endl;
    for vec in entries M do (
	for ent in vec do outFile << ent << " ";
	outFile << endl;
	);
    outFile << close;
    )

--pattern 1
A = matrix {{0, 0, 396, 108}, {0, 0, 4, 555}, {0, 470, 0, 812}, {455, 0, 0, 926}, {194, 761, 550, 0}}
B = matrix {{0, 260, 681, 695, 985}, {847, 0, 978, 543, 366}, {217, 522, 0, 851, 191}, {169, 208, 874, 0, 13}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)

--pattern 2
A=matrix{{0,0,221,407},{0,764,0,143},{0,444,918,0},{249,0,0,225},{189,336,27,0}}
B=matrix{{0,149,681,241,91},{275,0,979,759,958},{541,215,0,555,782},{224,872,233,0,51}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)

--pattern 3
A=matrix{{0,0,425,921},{0,472,0,80},{0,1,391,163},{862,0,98,0},{640,199,0,0}}
B=matrix{{0,5,361,894,927},{743,0,603,135,525},{93,825,0,580,538},{580,495,182,0,329}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)

--pattern 4
A=matrix{{0,0,356,9},{0,870,0,30},{0,302,469,731},{403,0,0,374},{852,190,147,0}}
B=matrix{{0,0,516,566,511},{422,73,0,719,675},{73,878,416,0,313},{545,816,186,97,0}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)

--pattern 5
A=matrix{{0,0,113,634},{0,671,0,562},{0,71,759,576},{697,0,0,270},{346,520,267,0}}
B=matrix{{401,724,0,736,848},{0,0,774,131,232},{896,850,255,0,178},{714,6,504,290,0}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)

--pattern 6
A = matrix {{0, 0, 525, 13}, {0, 106, 0, 751}, {0, 888, 56, 795}, {578, 0, 0, 500}, {568, 866, 720, 0}}
B = matrix {{742, 11, 0, 709, 983}, {76, 847, 839, 0, 759}, {557, 116, 45, 303, 0}, {0, 0, 612, 912, 566}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)

--pattern 7
A=matrix{{0,0,867,288},{0,112,0,295},{937,0,0,460},{832,102,761,0},{110,898,298,0}}
B=matrix{{0,0,319,786,898},{358,348,0,517,710},{72,243,286,0,702},{995,13,367,283,0}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)

--pattern 8
A=matrix{{0,0,454,713},{0,8,0,711},{288,0,0,926},{239,998,232,0},{541,37,830,0}}
B=matrix{{970,628,0,699,257},{277,527,733,0,824},{194,649,146,547,0},{0,0,831,918,343}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)

--pattern 9
A=matrix{{0,0,867,753},{0,211,0,189},{429,0,553,0},{556,864,0,0},{552,270,738,923}}
B=matrix{{0,0,207,28,502},{541,186,0,949,75},{596,13,966,0,459},{573,946,161,786,0}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)

--pattern 10
A=matrix{{0,0,239,284},{0,351,0,893},{86,0,215,0},{598,954,0,175},{154,545,31,0}}
B=matrix{{0,0,526,75,637},{474,360,0,531,603},{987,31,798,0,228},{100,288,777,74,0}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)

--pattern 11
A=matrix{{0,0,870,323},{0,21,0,201},{139,0,789,0},{623,36,0,556},{639,911,480,0}}
B=matrix{{892,249,0,272,965},{977,96,242,0,639},{0,0,104,856,217},{10,323,991,406,0}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)

--pattern 12
A=matrix{{0,0,523,41},{0,510,0,565},{772,0,0,556},{64,656,417,0},{853,13,77,901}}
B=matrix{{0,0,867,576,298},{0,718,0,550,66},{111,228,949,0,496},{151,9,123,923,0}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)

--pattern 13
A=matrix{{0,0,276,756},{0,656,0,784},{901,0,619,16},{440,202,0,669},{135,493,539,0}}
B=matrix{{0,0,975,71,387},{0,703,0,303,29},{837,288,837,0,613},{105,153,115,651,0}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)

--pattern 14 
A=matrix{{0,0,76,822},{0,433,0,644},{490,0,308,79},{934,626,0,570},{831,377,539,0}}
B=matrix{{0,0,495,221,68},{788,651,208,0,584},{950,66,251,994,0},{0,842,0,141,307}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)

--pattern 15
A=matrix{{0,0,236,707},{0,702,0,686},{849,0,507,136},{684,725,0,470},{47,914,326,0}}
B=matrix{{339,109,235,0,576},{0,0,787,588,128},{0,865,0,132,907},{395,100,265,883,0}}
M=matrix constructDualVectors(A,B)
outFile = "/Users/kubjask1/Dropbox/nonnegative_rank_boundaries/programs/Normaliz/normaliz_input.in"
makeNormalizFile(M,outFile)


