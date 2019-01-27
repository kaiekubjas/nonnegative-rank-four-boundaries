# nonnegative-rank-four-boundaries
This repository contains computations for the article "Nonnegative rank four boundaries" by Robert Krone and Kaie Kubjas. 

## Macaulay2 code: constructAllZeroPatterns.m2
This code constructs orbit representatives for all zero patterns with 13 zeros that satisfy the conditions of Theorem 4.4 and Lemma 4.7 in the paper such that every row of A contains a zero, and the number of columns of B is five or every column of B contains a zero.

## Macaulay2 code: constructNormalizInputForInfinitesimalRigidityCheck.m2
This code takes as an input a nonnegative matrix factorization and outputs an input for Normaliz for checking if the nonnegative decomposition is infinitesimally rigid. The Normaliz input is the dual of the cone W_(A,B).

## MATLAB code: findInfinitesimallyRigidConfigurations.m
This code constructs for each of the 15 zero patterns that satisfy the conditions of Theorem 4.4 for 5x5 matrices of nonnegative rank four 10000 realizations of nonnegative factorizations (A,B). Then it uses a nonnegative matrix factorization algorithm by Vandaele, Gillis, Glineur and Tuyttens to find a nonnegative factorization of AB. If this algorithm returns a factorization with 13 zeros or it cannot find a nonnegative factorization, the factorization (A,B) is a candidate for an infinitesimally rigid factorization. All candidates with the original and final factorizations are recorded.

## Mathematica code: locallyButNotInfintesimallyRigidExample.nb
This code checks the statements about the locally but not infinitesimally rigid example in the paper.

## MATLAB code: severalFactorizationsUsingMultistart.m
This code runs for each of the $15$ matrices with infinitesimally rigid factorizations the program by Vandaele, Gillis, Glineur and Tuyttens with the multistart heuristic ms1 ten times. In each of the cases, either this program could not find a nonnegative factorization of specified accuracy or it would find the nonnegative factorization that we started with.
