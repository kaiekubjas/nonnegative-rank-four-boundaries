% one needs to add paths to the folders '/heurExactNMF', '/heurExactNMF/code' and 'heurExactNMF/code/algosNMF'

r=4;
nRuns=10;

%options of the nonnegative factorization algorithm
options.heuristic = 'ms1';
options.maxiter = 5;

%matrix
M = [104184 229176 94392 336996 77040;
     94663 117528 485070 3404 7979;
     535318 168896 1169348 255210 182576;
     156494 310908 1119179 316225 460213;
     763917 337540 876372 1016103 574666];

M = [210729 402419 94831 122655 193579;
     242132 124696 781275 579876 739205;
     618738 197370 434676 846486 1143228;
     50400 233301 221994 60009 34134;
     107007 33966 457653 315558 360201];

M = [573705 806520 167622 246500 531659;
     397096 39600 299176 63720 274120;
     131646 403260 30269 226915 264510;
     9114 85160 311182 827468 851798;
     147857 3200 351037 599025 697755];

M = [30893 319912 149770 873 111428;
     383490 87990 5580 628440 587250;
     560076 1030324 331070 288045 350647;
     203830 305184 277512 264376 205933;
     90911 142936 500784 618842 609633];

M = [553924 99854 348351 183860 20114;
     401268 3372 802602 250881 155672;
     1091328 648606 538803 176341 151574;
     472277 506248 136080 591292 591056;
     377978 477454 470565 322776 461574];

M = [292425 60900 31581 170931 7358;
     8056 89782 548546 684912 505520;
     98680 758632 1234092 742008 1123962;
     428876 6358 306000 865802 851174;
     888312 823270 758974 620872 1215638];

M = [348984 214425 353658 81504 608634;
     333621 42811 108265 141389 79520;
     457700 5980 467723 866662 841426;
     91308 220419 483054 706686 1353778;
     342940 384918 120318 550726 945556];

M = [88076 294646 658787 902872 244559;
     2216 4216 596705 652698 250465;
     279360 180864 769506 1051380 391634;
     553284 826606 765406 293965 883775;
     696039 897917 148301 832169 169525];

M = [948201 723609 958755 591858 397953;
     222448 218040 30429 348793 15825;
     329588 7189 623001 12012 469185;
     467424 160704 115092 835504 343912;
     1114797 932972 975775 997164 636096];

M = [264293 89201 411390 21016 54492;
     255674 383544 693861 252463 211653;
     212205 6665 216806 6450 103802;
     469696 393840 450523 564374 956188;
     288927 197161 105742 300945 433801];

M = [3230 104329 410573 875858 188790;
     22527 66939 204273 81606 13419;
     123988 34611 82056 713192 305348;
     596448 338171 559708 395192 624199;
     1460035 246567 270382 584688 1302924];

M = [64244 119613 501370 37843 259408;
     85315 371265 69495 801995 33660;
     83956 5004 737712 957860 230056;
     46287 566084 451221 397664 269200;
     144598 34999 923447 1330101 293244];

M = [310392 195156 317952 492156 169188;
     82320 581120 90160 709152 19024;
     519783 180720 1398418 74387 728134;
     70245 244363 505935 527965 176138;
    451143 501811 582768 158964 396949];

M = [72200 697140 19076 191446 252354;
     341204 824131 90064 90804 450580;
     292600 86846 319858 425581 57573;
     493288 887466 592538 286784 604086;
     809126 281001 625050 719417 276676];

M = [279265 274840 187355 655433 214052;
     270970 68600 734264 1018514 89856;
     341531 544696 235555 187012 948873;
     417526 121556 855865 841310 486784;
     15933 287113 730363 580464 439746];

MMatrix=[];
WMatrix=[];
HMatrix=[];

% For reproducibility
rng default

for j=1:nRuns
        [W H e] = exactNMFheur(M,r,options);
        MMatrix(j,:,:)=M(:,:);
        WMatrix(j,:,:)=W(:,:);
        HMatrix(j,:,:)=H(:,:);
end
