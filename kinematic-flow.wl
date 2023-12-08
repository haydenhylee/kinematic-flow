(* ::Package:: *)

(* ::Section:: *)
(*Definitions*)


(* ::Subsubsection:: *)
(*Simplex forms*)


t[a__]:=\[LeftAngleBracket]a\[RightAngleBracket]
tt[a__]:=Abs@sign[a]t[a](*vanishes if the planes don't intersect*)
ord[f_]:=f/.\[LeftAngleBracket]a__\[RightAngleBracket]:>Signature[{a}]t@@Sort[{a}]


(*boundary of a simplex*)
bdry[expr_]:=expr/.\[LeftAngleBracket]a__\[RightAngleBracket]:>Sum[(-1)^(j+1) Delete[\[LeftAngleBracket]a\[RightAngleBracket],j],{j,Length@\[LeftAngleBracket]a\[RightAngleBracket]}]


(*relative sign between \[LeftAngleBracket]12\[Ellipsis]\[RightAngleBracket] and (Subscript[dx, 1]\[Wedge]Subscript[dx, 2]\[Wedge]\[Ellipsis])/(Subscript[L, 1]Subscript[L, 2]\[Ellipsis])*)
sign[a__]:=dlog[a]Times@@(planes[[#]]&/@{a})//Simplify


(*evaluate \[LeftAngleBracket]12\[Ellipsis]\[RightAngleBracket]=dlog Subscript[L, 1]\[Wedge]dlog Subscript[L, 2]\[Wedge]\[Ellipsis]*)
dlog[a__]:=w@@(Dt@Log@planes[[#]]&/@{a})
eval[f_]:=f/.\[LeftAngleBracket]a__\[RightAngleBracket]:>dlog@@{a}//Simplify


(*turn equation in symbolic form*)
symeq=Coefficient[#/. 1/a_:>Log[a],func]&;


(* ::Subsubsection:: *)
(*Source functions*)


replace[a_,i_][f_]:=f/. a->i/.AngleBracket->tt//ord
replace[list_List,i_][f_]:=f/. Table[Rule[list[[n]],i],{n,Length@list}]/.AngleBracket->tt//ord


funcTree[list_]:=Block[{graph,funcs,Nsite},
Nsite=Length@list[[-1]];
graph=ResourceFunction["HasseDiagram"][SubsetQ[#2,#1]&,list,VertexShapeFunction->"Name",GraphLayout->"LayeredDigraphEmbedding"];
funcs=Length@Cases[list,#]&/@Table[_,{i,0,Nsite},{j,i}];
Print[graph];
Grid[{Prepend[Table[i,{i,0,Nsite}],"# twists"],
Prepend[funcs,"# functions"]},Frame->All]
]


(* ::Subsubsection:: *)
(*Total differential*)


(*total differential of a dlog form (wrt Subscript[X, i])*)
totd[f_]:=f/.\[LeftAngleBracket]a__\[RightAngleBracket]:>Sum[(*Simplify@*)Dt@(Log@@({Det@(P/@{a,j})}/.flip))bdry@\[LeftAngleBracket]a,j\[RightAngleBracket],{j,Length@planes-Length@\[LeftAngleBracket]a\[RightAngleBracket]+1,Length@planes}]/.\[LeftAngleBracket]a__\[RightAngleBracket]:>Signature[{a}]tt@@Sort[{a}]
dX[X_]:=Collect[Coefficient[totd@#,Dt[X]],1/letters,Simplify]&


(*list of planes*)
plist[f_]:=List@@f/.\[LeftAngleBracket]a__\[RightAngleBracket]:>{a}//Abs//Flatten//Sort//DeleteDuplicates
totdX[f_]:=Collect[f/.\[LeftAngleBracket]a__\[RightAngleBracket]:>Sum[dL@@(Log@@({Det@(P/@{j,a})}/.flip))bdry@\[LeftAngleBracket]j,a\[RightAngleBracket],{j,Length@planes-Length@\[LeftAngleBracket]a\[RightAngleBracket]+1,Length@planes}]/.\[LeftAngleBracket]a__\[RightAngleBracket]:>Signature[{a}]tt@@Sort[{a}]/.dL[a__]:>Subscript[dL, a],Subscript[dL, ___],Simplify]


dLsimp[wprod_]:=Collect[Expand@wprod/.Subscript[dL, X1_]\[Wedge]Subscript[dL, X2_]:>Signature[{X1,X2}]Subscript[dL, Sort[{X1,X2}][[1]]]\[Wedge]Subscript[dL, Sort[{X1,X2}][[2]]],Subscript[f, _],Simplify]
dd[expr_]:=Collect[Expand[d[expr]/.dfsub]/.Subscript[f, a_]b_:>d[Subscript[f, a]]\[Wedge]b/.dfsub,Subscript[f, _],Simplify]//dLsimp
ddnosimp[expr_]:=Collect[Expand[d[expr]/.dfsub]/.Subscript[f, a_]b_:>d[Subscript[f, a]]\[Wedge]b/.dfsub,Subscript[f, _],Simplify]


solveCoeff:=Do[
Subscript[dLs, nn[[l]][[m]]]=Cases[totdX@Subscript[F, nn[[l]][[m]]],Subscript[dL, ___],\[Infinity]];
Subscript[dLco, nn[[l]][[m]]]=Coefficient[totdX@Subscript[F, nn[[l]][[m]]],Subscript[dLs, nn[[l]][[m]]]];
Subscript[dLcosol, nn[[l]][[m]]]=Flatten@Table[Solve[0==(List@@Collect[Subscript[dLco, nn[[l]][[m]]][[n]]-Sum[Subscript[d, nn[[l]][[m]]][n,j]Subscript[F, nn[[l]][[j]]],{j,Length@nn[[l]]}]-(1-KroneckerDelta[nsite+1,l])Sum[Subscript[c, nn[[l]][[m]]][n,j]Subscript[F, nn[[l+1]][[j]]],{j,Length@nn[[l+1]]}]/.\[LeftAngleBracket]a__\[RightAngleBracket]:>ord@\[LeftAngleBracket]a\[RightAngleBracket],\[LeftAngleBracket]__\[RightAngleBracket]]/.\[LeftAngleBracket]__\[RightAngleBracket]->1)],{n,1,Length@Subscript[dLco, nn[[l]][[m]]]}]
,{l,nsite+1},{m,Length@nn[[l]]}]//Quiet;


eqlvl[i_]:=Flatten[Table[d[Subscript[f, nn[[l]][[m]]]]==Sum[(Sum[Subscript[d, nn[[l]][[m]]][n,j]Subscript[f, nn[[l]][[j]]],{j,Length@nn[[l]]}]+(1-KroneckerDelta[nsite+1,l])Sum[Subscript[c, nn[[l]][[m]]][n,j]Subscript[f, nn[[l+1]][[j]]],{j,Length@nn[[l+1]]}])Subscript[dLs, nn[[l]][[m]]][[n]]/.Subscript[dLcosol, nn[[l]][[m]]],{n,Length@Subscript[dLco, nn[[l]][[m]]]}],{l,{i}},{m,Length@nn[[l]]}],1]/.\!\(\*SubscriptBox[\(f\), \({
\*SubscriptBox[\(1\), \(a_\)], 
\*SubscriptBox[\(2\), \(b_\)]}\)]\):>0/;a=!=b//Quiet//DeleteCases[d[0]==0]


(* ::Subsubsection:: *)
(*Wedge product*)


(*w[Subscript[L, 1],\[Ellipsis]]=(Subscript[dL, 1]\[Wedge]\[Ellipsis])/(Subscript[dx, 1]\[Wedge]\[Ellipsis])*)
w[v__]:=Signature[{##}]Product[Coefficient[{v}[[n]],Dt[{##}[[n]]]],{n,Length@{v}}]&@@@(Permutations@Table[Symbol["x"<>ToString@j],{j,Length@{v}}])//Total
wX[v__]:=Signature[{##}]Product[Coefficient[{v}[[n]],Dt[{##}[[n]]]],{n,Length@{v}}]&@@@(Permutations@Table[Symbol["X"<>ToString@j],{j,Length@{v}}])//Total


(*Wedge product properties:*)
a_\[Wedge]a_:=0
a_\[Wedge](b_+c_):=a\[Wedge]b+a\[Wedge]c
a_\[Wedge]((b_+c_)/d_):=a\[Wedge]b/d+a\[Wedge]c/d
(a_+b_)\[Wedge]c_:=a\[Wedge]c+b\[Wedge]c
((a_+b_)/d_)\[Wedge]c_:=a/d\[Wedge]c+b/d\[Wedge]c
(-a_)\[Wedge]c_:=-(a\[Wedge]c)
a_\[Wedge](-c_):=-(a\[Wedge]c)
(f_ Subscript[dL, x_])\[Wedge]c_:=f(Subscript[dL, x]\[Wedge]c)
c_\[Wedge](f_ Subscript[dL, x_]):=f(c\[Wedge]Subscript[dL, x])
(z_ Subscript[f, a_])\[Wedge]c_:=Subscript[f, a](z\[Wedge]c)


(* ::Subsubsection:: *)
(*Tensor product*)


TensorSimp[expr_]:=expr//.a_\[CircleTimes](b_-c_):>a\[CircleTimes]b-a\[CircleTimes]c//.a_\[CircleTimes](b_+c_):>a\[CircleTimes]b+a\[CircleTimes]c//.
(b_-c_)\[CircleTimes]a_:>b\[CircleTimes]a-c\[CircleTimes]a//.(b_+c_)\[CircleTimes]a_:>b\[CircleTimes]a+c\[CircleTimes]a//.
(a_\[CircleTimes]b_)\[CircleTimes]c_:>a\[CircleTimes]b\[CircleTimes]c//.a_\[CircleTimes](b_\[CircleTimes]c_):>a\[CircleTimes]b\[CircleTimes]c//.
(c_. \[CapitalPhi][c1_])/\[CapitalPhi][c2_]\[CircleTimes]\[CapitalPhi][c3_]/\[CapitalPhi][c4_]\[CircleTimes]\[CapitalPhi][c5_]/\[CapitalPhi][c6_]:>c((\[CapitalPhi][c1]\[CircleTimes]\[CapitalPhi][c3]\[CircleTimes]\[CapitalPhi][c5]-\[CapitalPhi][c1]\[CircleTimes]\[CapitalPhi][c3]\[CircleTimes]\[CapitalPhi][c6]-\[CapitalPhi][c1]\[CircleTimes]\[CapitalPhi][c4]\[CircleTimes]\[CapitalPhi][c5]+\[CapitalPhi][c1]\[CircleTimes]\[CapitalPhi][c4]\[CircleTimes]\[CapitalPhi][c6])-(\[CapitalPhi][c2]\[CircleTimes]\[CapitalPhi][c3]\[CircleTimes]\[CapitalPhi][c5]-\[CapitalPhi][c2]\[CircleTimes]\[CapitalPhi][c3]\[CircleTimes]\[CapitalPhi][c6]-\[CapitalPhi][c2]\[CircleTimes]\[CapitalPhi][c4]\[CircleTimes]\[CapitalPhi][c5]+\[CapitalPhi][c2]\[CircleTimes]\[CapitalPhi][c4]\[CircleTimes]\[CapitalPhi][c6]))
