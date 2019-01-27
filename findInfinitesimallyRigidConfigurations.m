% one needs to add paths to the folders '/heurExactNMF', '/heurExactNMF/code' and 'heurExactNMF/code/algosNMF'

m=5;
n=5;
r=4;
nRuns=10000;

%options of the nonnegative factorization algorithm
options.heuristic = 'rbr';
options.maxiter = 10;

% all possible zero patterns
zeroPatterns = [
                'U(1,1)=0; U(2,1)=0; U(3,1)=0; U(1,2)=0; U(2,2)=0; U(4,2)=0; U(3,3)=0; U(4,3)=0; U(5,4)=0; V(1,1)=0; V(2,2)=0; V(3,3)=0; V(4,4)=0; ';
                'U(1,1)=0; U(2,1)=0; U(3,1)=0; U(1,2)=0; U(4,2)=0; U(2,3)=0; U(4,3)=0; U(3,4)=0; U(5,4)=0; V(1,1)=0; V(2,2)=0; V(3,3)=0; V(4,4)=0; ';
                'U(1,1)=0; U(2,1)=0; U(3,1)=0; U(1,2)=0; U(4,2)=0; U(2,3)=0; U(5,3)=0; U(4,4)=0; U(5,4)=0; V(1,1)=0; V(2,2)=0; V(3,3)=0; V(4,4)=0; ';
                'U(1,1)=0; U(2,1)=0; U(3,1)=0; U(1,2)=0; U(4,2)=0; U(2,3)=0; U(4,3)=0; U(5,4)=0; V(1,1)=0; V(1,2)=0; V(2,3)=0; V(3,4)=0; V(4,5)=0; ';
                'U(1,1)=0; U(2,1)=0; U(3,1)=0; U(1,2)=0; U(4,2)=0; U(2,3)=0; U(4,3)=0; U(5,4)=0; V(1,3)=0; V(2,1)=0; V(2,2)=0; V(3,4)=0; V(4,5)=0; ';
                'U(1,1)=0; U(2,1)=0; U(3,1)=0; U(1,2)=0; U(4,2)=0; U(2,3)=0; U(4,3)=0; U(5,4)=0; V(1,3)=0; V(2,4)=0; V(3,5)=0; V(4,1)=0; V(4,2)=0; ';
                'U(1,1)=0; U(2,1)=0; U(1,2)=0; U(3,2)=0; U(2,3)=0; U(3,3)=0; U(4,4)=0; U(5,4)=0; V(1,1)=0; V(1,2)=0; V(2,3)=0; V(3,4)=0; V(4,5)=0; ';
                'U(1,1)=0; U(2,1)=0; U(1,2)=0; U(3,2)=0; U(2,3)=0; U(3,3)=0; U(4,4)=0; U(5,4)=0; V(1,3)=0; V(2,4)=0; V(3,5)=0; V(4,1)=0; V(4,2)=0; ';
                'U(1,1)=0; U(2,1)=0; U(1,2)=0; U(3,2)=0; U(2,3)=0; U(4,3)=0; U(3,4)=0; U(4,4)=0; V(1,1)=0; V(1,2)=0; V(2,3)=0; V(3,4)=0; V(4,5)=0; ';
                'U(1,1)=0; U(2,1)=0; U(1,2)=0; U(3,2)=0; U(2,3)=0; U(4,3)=0; U(3,4)=0; U(5,4)=0; V(1,1)=0; V(1,2)=0; V(2,3)=0; V(3,4)=0; V(4,5)=0; ';
                'U(1,1)=0; U(2,1)=0; U(1,2)=0; U(3,2)=0; U(2,3)=0; U(4,3)=0; U(3,4)=0; U(5,4)=0; V(1,3)=0; V(2,4)=0; V(3,1)=0; V(3,2)=0; V(4,5)=0; ';
                'U(1,1)=0; U(2,1)=0; U(1,2)=0; U(3,2)=0; U(2,3)=0; U(3,3)=0; U(4,4)=0; V(1,1)=0; V(1,2)=0; V(2,1)=0; V(2,3)=0; V(3,4)=0; V(4,5)=0; ';
                'U(1,1)=0; U(2,1)=0; U(1,2)=0; U(3,2)=0; U(2,3)=0; U(4,3)=0; U(5,4)=0; V(1,1)=0; V(1,2)=0; V(2,1)=0; V(2,3)=0; V(3,4)=0; V(4,5)=0; ';
                'U(1,1)=0; U(2,1)=0; U(1,2)=0; U(3,2)=0; U(2,3)=0; U(4,3)=0; U(5,4)=0; V(1,1)=0; V(1,2)=0; V(2,4)=0; V(3,5)=0; V(4,1)=0; V(4,3)=0; ';
                'U(1,1)=0; U(2,1)=0; U(1,2)=0; U(3,2)=0; U(2,3)=0; U(4,3)=0; U(5,4)=0; V(1,4)=0; V(2,1)=0; V(2,2)=0; V(3,1)=0; V(3,3)=0; V(4,5)=0; ';
                ];
zeroPatterns = string(zeroPatterns);

for i=1:length(zeroPatterns)

    AMatrix=[];
    UMatrix=[];
    VMatrix=[];
    WMatrix=[];
    HMatrix=[];
    eMatrix=[];
    k=0;

    % For reproducibility
    rng default

    for j=1:nRuns
        % construct random matrices U and V
        U=randi([1,100],m,r);
        V=randi([1,100],r,n);
        % set entries corresponding to the zero pattern to zero
        eval(char(zeroPatterns(i))); 
        % let A be the product of U and V
        A=U*V;
        % check if A has nonnegative rank at most 4 and find a nonnegative rank
        % factorization
        [W H e] = exactNMFheur(A,4,options);
        % count zeros
        nZeros=sum(W(:)<10^(-1))+sum(H(:)<10^(-1));
        % if the number of zeros is 13, then print the factors
        if (nZeros==13) | (e(1)>=10^(-5))
            disp(nZeros)
            k=k+1;
            AMatrix(k,:,:)=A(:,:);
            UMatrix(k,:,:)=U(:,:);
            VMatrix(k,:,:)=V(:,:);
            WMatrix(k,:,:)=W(:,:);
            HMatrix(k,:,:)=H(:,:);
            eMatrix(k)=e(1);
        end
    end

    % save the results to file
    outfile = sprintf('boundary-candidates-%dx%d-%d.mat',m,n,i);
    save(outfile,'AMatrix', 'UMatrix', 'VMatrix', 'WMatrix', 'HMatrix', 'eMatrix');
end
