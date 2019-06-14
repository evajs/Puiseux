(* Mathematica Package *)

(* Created by the Wolfram Workbench 1.10.2014 *)

BeginPackage["Puiseux`"]
(* Exported symbols added here with SymbolName::usage *) 


PlotNewton::usage = 
  "PlotNewton[f] generates graph of Newton polygon of f returns graph of its Newton polygon.";
  (*PositiveSlope -> True admit all graph, False only the part of Newton polygon with negative slope.*)

PlotNewton::vars = "Argument is polynomial in `1` variables, two variables expected."

EdgesNewton::usage = 
  "EdgesNewton[f] generates list of edge of Newton polygon of f given by its points.";
  (*PositiveSlope -> True admit all graph, False only the part of Newton polygon with negative slope.*)
  (*All -> True returns all points on every edge.*)

EdgesNewton::vars = "Argument is polynomial in `1` variables, two variables expected."

PolygonNewton::usage = 
  "PolygonNewton[f, z] generate list of edges of Newton polygon of f. Every edges {e_1, e_2, e_3, e_4} is represented by its normal (e_1, e_2, -e_3) and characteristic polynomial e_4 in given variable z.";
 (*PositiveSlope -> True admit all graph, False only the part of Newton polygon with negative slope.*)
 
PolygonNewton::vars = "First argument is polynomial in `1` variables, two variables expected."
 
PuiseuxExpansion::usage = 
  "PuiseuxExpansion[f] generate list of Puiseux expansions of branches of f at the origin.
  PuiseuxExpansion[f, {x,y}] generate list of Puiseux expansions of branches of f at the point (x,y).";

PuiseuxExpansion::vars = "First argument is polynomial in `1` variables, two variables expected."

Begin["`Private`"]
(* Implementation of the package *)

Needs["ComputationalGeometry`"];

verticesNewton[f_] := Module[{variables},
   variables = Variables[f];
   {Exponent[#, variables[[2]]], Exponent[#, variables[[1]]]} & /@ 
    MonomialList[f]];

Options[PlotNewton] = {PositiveSlope -> True};
PlotNewton[f_, OptionsPattern[]] := Module[
   {vertices, ticks, edges, variables, out},
   variables = Variables[f];
   
   If[Length[variables]!=2, Message[PlotNewton::vars, Length[variables]];out = f,
   vertices = verticesNewton[f];
   ticks = {Range[ Min[Transpose[vertices][[1]]], 
      Max[Transpose[vertices][[1]]]], 
     Range[ Min[Transpose[vertices][[2]]], 
      Max[Transpose[vertices][[2]]]]};
   edges = 
    lowerEdges[vertices, All -> False, 
     PositiveSlope -> OptionValue[PositiveSlope]];
   out = Show[ListPlot[vertices, 
     AxesLabel -> {variables[[2]], variables[[1]]}, 
     AspectRatio -> Automatic, PlotStyle -> PointSize[Medium], 
     Ticks -> ticks], ListLinePlot[edges]]];
   out
   ];

Options[EdgesNewton] = {PositiveSlope -> True, All -> False};
EdgesNewton[f_, OptionsPattern[]] := 
Module[{variables, out},
	variables=Variables[f];
	If[Length[variables]!=2, Message[EdgesNewton::vars, Length[variables]];out = f,
  out = lowerEdges[verticesNewton[f], PositiveSlope -> OptionValue[PositiveSlope], 
   All -> OptionValue[All]]];
   out];

Options[PolygonNewton] = {PositiveSlope -> True};
PolygonNewton[f_, z_, OptionsPattern[]] := 
  Module[{lowerHullEdges, coeficients, variables, out},
   variables = Variables[f];
   
   If[Length[variables]!=2, Message[PuiseuxExpansion::vars, Length[variables]];out = f,
   lowerHullEdges = 
    lowerEdges[verticesNewton[f], 
     PositiveSlope -> OptionValue[PositiveSlope]];
   coeficients = 
    CoefficientList[f, {variables[[1]], variables[[2]]}];
  
  (*polygonEdges=*)
  out=
    Table[Append[edge[1, 2, lowerHullEdges[[i]]][[{2, 1, 3}]], 
      Sum[coeficients[[lowerHullEdges[[i, j, 2]] + 1, 
          lowerHullEdges[[i, j, 1]] + 1]]*
        z^(lowerHullEdges[[i, j, 1]]/
           edge[1, 2, lowerHullEdges[[i]]][[2]]), {j, 1, 
        Length[lowerHullEdges[[i]]]}]], {i, 1, 
      Length[lowerHullEdges]}]];
   out
   ];


(*bezout: to list {a,b} assigns list {c,d} such that {a,b}.{c,d}*)
bezout[list_List] := 
  Module[{x, y}, {x, y} /. 
    Flatten[FindInstance[list[[1]] x + list[[2]] y == 1, {x, y}, Integers]]
   ];

(*edge: from points at positions i, j in list make coefficients of normal {a,b,-c} of line connecting them*)
edge[i_, j_, list_] := Module[{abc, a, b, c},
   abc = Flatten[
     FindInstance[{a list[[i, 1]] + b list[[i, 2]] - c == 0, 
       a list[[j, 1]] + b list[[j, 2]] - c == 0, 
       Not[a == 0 && b == 0 && c == 0], b >= 0}, {a, b, c}, Integers]];
   ({a, b, c} /. abc)/GCD[Sequence @@ ({a, b, c} /. abc)]
   ];

(*halfHull make from points two parts between positions of LLC and RLC*)
halfHull[points_, positionLeftLowerCorner_, positionRightLowerCorner_] :=
   Module[{halfHullPts1, halfHullPts2}, 
   halfHullPts1 = 
    If[positionLeftLowerCorner < positionRightLowerCorner, 
     Table[points[[i]], {i, positionLeftLowerCorner, 
       positionRightLowerCorner}], 
     Reverse[Table[
       points[[i]], {i, positionRightLowerCorner, 
        positionLeftLowerCorner}]]];
   halfHullPts2 = 
    If[positionLeftLowerCorner < positionRightLowerCorner, 
     Reverse[Join[
       Table[points[[i]], {i, positionRightLowerCorner, Length[points]}], 
       Table[points[[i]], {i, 1, positionLeftLowerCorner}]]], 
     Join[Table[
       points[[i]], {i, positionLeftLowerCorner, Length[points]}], 
      Table[points[[i]], {i, 1, positionRightLowerCorner}]]];
   {halfHullPts1, halfHullPts2}];

(*lowerHullQ test whether halfHull should be lower convex hull*)
lowerHullQ[halfHull_] := 
 Module[{edgeFirstLast}, edgeFirstLast = edge[1, Length[halfHull], halfHull];
  If[((edgeFirstLast[[{1, 2}]].halfHull[[2]]) - edgeFirstLast[[3]]) < 0, True, False]]

(*firstHalfHullQ test whether halfHullPts1 or halfHullPts2 is lower convex hull (assuming that one of them is)*)

chooseHalfHull[halfHullPts1_, halfHullPts2_] :=
  Module[{firstHalf},
   If[Length[halfHullPts1] > 2 && lowerHullQ[halfHullPts1],
    firstHalf = halfHullPts1,
    If[Length[halfHullPts2] > 2 && lowerHullQ[halfHullPts2],
     firstHalf = halfHullPts2,
     If[Length[halfHullPts1] == 2,
      firstHalf = halfHullPts1,
      firstHalf = halfHullPts2]]];
   firstHalf
   ];

leftLowerCornerPoint[hullPts_]:=
First[Sort[
      hullPts, (#1[[1]] < #2[[1]]) || (#1[[1]] == #2[[1]] && #1[[2]] \
< #2[[2]]) &]];

rightLowerCornerPoint[hullPts_]:=
First[Sort[
      hullPts, (#1[[1]] > #2[[1]]) || (#1[[1]] == #2[[1]] && #1[[2]] \
< #2[[2]]) &]];

(*lowerEdges: For points return the list of edges of lower convex hull.*)
Options[lowerEdges] = {All -> True, PositiveSlope -> True};
lowerEdges[points_, OptionsPattern[]] :=
  
  Module[{hullPositions, hullPts, hullAllPositions, hullAllPts, 
  	pointLeftLowerCorner, positionLeftLowerCorner, pointRightLowerCorner, 
    positionRightLowerCorner, 
    halfHullPts1, halfHullPts2, halfHullAllPts1, halfHullAllPts2, lowerHullAllPts, lowerHullPts, lowerHullEdges},
    
   hullPositions = ConvexHull[points, AllPoints -> False];
   hullPts = points[[#]] & /@ hullPositions;
   If[OptionValue[All],
    hullAllPositions = ConvexHull[points, AllPoints -> True];
    hullAllPts = points[[#]] & /@ hullAllPositions;
    ,(*else*)
    hullAllPositions = hullPositions;
    hullAllPts = hullPts;
    ];

   pointLeftLowerCorner = leftLowerCornerPoint[hullPts];
   positionLeftLowerCorner = 
    Flatten[Position[hullPts, pointLeftLowerCorner]][[1]];
   positionLeftLowerCornerAll = 
    Flatten[Position[hullAllPts, pointLeftLowerCorner]][[1]];

   pointRightLowerCorner = rightLowerCornerPoint[hullPts];
   positionRightLowerCorner = 
    Flatten[Position[hullPts, pointRightLowerCorner]][[1]];
   positionRightLowerCornerAll = 
    Flatten[Position[hullAllPts, pointRightLowerCorner]][[1]];
   
   {halfHullPts1, halfHullPts2} = 
    halfHull[hullPts, positionLeftLowerCorner, 
     positionRightLowerCorner];
   {halfHullAllPts1, halfHullAllPts2} = 
    halfHull[hullAllPts, positionLeftLowerCornerAll, 
     positionRightLowerCornerAll];
   
    lowerHullPts = chooseHalfHull[halfHullPts1, halfHullPts2];
    (*Print[lowerHullPts];
    Print[halfHullAllPts1];Print[halfHullAllPts2];*)
   
    lowerHullAllPts = chooseHalfHull[halfHullAllPts1, halfHullAllPts2];
    (*Print[lowerHullAllPts];*)
    
   (*firstHalf = firstHalfHullQ[halfHullPts1, halfHullPts2];
   
   If[firstHalf,
    lowerHullPts = halfHullPts1;
    lowerHullAllPts = halfHullAllPts1;,
    lowerHullPts = halfHullPts2;
    lowerHullAllPts = halfHullAllPts2;];
    
    Print[lowerHullPts];
    Print[halfHullAllPts1];Print[halfHullAllPts2];
    Print[lowerHullAllPts];*)
   
   lowerHullEdges = Table[lowerHullAllPts[[
       Range[Position[lowerHullAllPts, lowerHullPts[[i]]][[1, 1]], 
         Position[lowerHullAllPts, lowerHullPts[[i + 1]]]][[1, 1]]
       ]],
     {i, 1, Length[lowerHullPts] - 1}];
     
    lowerHullEdges=Select[lowerHullEdges, (First[#][[2]] - 
          Last[#][[2]])*(First[#][[1]] - Last[#][[1]]) != 0 &];
 
   If[Not[OptionValue[PositiveSlope]], 
    Select[
          lowerHullEdges, (First[#][[2]] - 
          Last[#][[2]])*(First[#][[1]] - Last[#][[1]]) < 0 &], 
    lowerHullEdges]
   ];


(*squareFree: for polynomial f returns square free polynomial*)
squareFree[f_] := 
  Module[{factors}, factors = FactorSquareFreeList[f];
   Product[factors[[i, 1]], {i, 1, Length[factors]}]];


(*singularTerm: for newtonPolygon list with characteristic polynomials in variable z returns singular part
of Puiseux expansion in form {a, 1, b, root, c, factor}, where {a,b,c} are cofficient of edge of newtonPolygon*)
Options[singularTerm] = {Rational -> True};
singularTerm[newtonPolygon_, z_, OptionsPattern[]] := 
  Module[{roots, factors, out},
   (*z = Flatten[Union[Table[Variables[newton[[i,4]]],{i, 1, Length[
   newton]}]]][[1]]*)
   
   factors = 
    Table[FactorSquareFreeList[newtonPolygon[[i, 4]]], {i, 1, 
      Length[newtonPolygon]}];
   roots = 
    Table[Table[
      Solve[{factors[[i, j, 1]] == 0, z != 0}, z], {j, 1, 
       Length[factors[[i]]]}], {i, 1, Length[newtonPolygon]}];
   If[Not[OptionValue[Rational]], 
    out = Flatten[
      Table[Table[
        Table[Module[{beta}, 
          beta = u /. 
            Solve[squareFree[
               u^newtonPolygon[[l, 1]] - (z /. roots[[l, i, j]])] == 0, 
             u];
          Table[Prepend[{newtonPolygon[[l, 3]], 
             factors[[l, i, 2]]}, {newtonPolygon[[l, 1]], 1, 
             newtonPolygon[[l, 2]], beta[[k]]}], {k, 1, 
            Length[beta]}]], {j, 1, Length[roots[[l, i]]]}], {i, 
         1, Length[factors[[l]]]}], {l, 1, Length[newtonPolygon]}], 3]];
   If[OptionValue[Rational],
    out =
     Flatten[
      Table[
       Table[
        Table[Module[{u, v}, {u, v} = bezout[newtonPolygon[[l, {1, 2}]]];
          
          Prepend[{newtonPolygon[[l, 3]], 
            factors[[l, i, 2]]}, {newtonPolygon[[l, 
              1]], (z /. roots[[l, i, j]])^(-v), 
            newtonPolygon[[l, 2]], (z /. roots[[l, i, j]])^u}]], {j, 
          1, Length[roots[[l, i]]]}], {i, 1, 
         Length[factors[[l]]]}], {l, 1, Length[newtonPolygon]}], 2]];
   out];


(*co kdyz je length singular vetsi nez chci, zatim nedoreseno*)
(*singular: for polynomial, list of terms and list of extensions returns 
list of polynomial, list of terms, list of extensions of whole singular part.*)
singular::nmbr="Input polynomial has only one summand";
Options[singular] = {Rational -> True};
singular[ f_, pi_, extension_, OptionsPattern[]] := 
  Module[{verticesList,
     lowerHullEdges, newtonPolygon, singularTerms, out, positiveSlope, pi1, f1, 
    extension1, i, variables, z},
   variables = Variables[f];
   If [Length[pi] == 0, positiveSlope = True, positiveSlope = False];
   verticesList = verticesNewton[f];
   
   If[Length[verticesList]==1,Message[Singular::nmbr],
   	
   lowerHullEdges = lowerEdges[verticesList];
   
   newtonPolygon = PolygonNewton[f, z, PositiveSlope -> positiveSlope];
   
   singularTerms := 
    singularTerm[newtonPolygon, z, 
     Rational -> OptionValue[Rational]];
   
   out = {};
   For[i = 1, i <= Length[singularTerms], i++,
    pi1 = Append[pi, singularTerms[[i, 1]]];
    f1 = Collect[
      Expand[variables[[1]]^(-singularTerms[[i, 
             2]])*(f /. {variables[[1]] -> (singularTerms[[i, 
                1, 2]]*variables[[1]]^singularTerms[[i, 1, 1]]), 
           variables[[2]] -> (variables[[1]]^
               singularTerms[[i, 1, 3]]*(singularTerms[[i, 1, 4]] + 
                variables[[2]]))})], variables[[2]]];
    
    extension1 = 
     Cases[Union[Flatten[Append[extension, singularTerms[[i, 1, {2, 4}]]]]], Except[-1 | 1 | _Rational|_Integer]];
    If[Not[singularTerms[[i, 3]] == 1],
     out = Join[out, 
        singular[f1, pi1, extension1, 
         Rational -> OptionValue[Rational]]];,
     out = Append[out, {f1, pi1, extension1}];
     ]
    ];];
   out
   ];

(*regular: for list singularPart and lenght of expansion returns list of terms of given length*)
regular[singularPart_, expansionLength_] :=
  
  Module[{out, iteration, pi, f, m, beta, coeficientPolynom, tau, 
    extension, variables, vertices, time},
   out = {};
   For[iteration = 1, iteration <= Length[singularPart], iteration++,
    {f, pi, extension} = singularPart[[iteration]];
    variables = Variables[f];
    While[Length[pi] < expansionLength,
    {time,vertices} = Timing[verticesNewton[f]];
    (*Print[f];
    Print[vertices];*)
    (*Print[Length[pi]," 1 ",time];*)
     m = First[
        Sort[Select[vertices(*y,
          x*), #[[1]] == 0 &], #1[[2]] < #2[[2]] &]][[2]];
 	(*Print[Length[pi],"2"];*)
     coeficientPolynom = CoefficientList[f, {variables[[1]], variables[[2]]}];
     (*Print[Length[pi],"3"];*)
     (*beta = 0;
     beta := -coeficientPolynom[[m + 1, 1]]/
       coeficientPolynom[[1, 1 + 1]]/;((Length[coeficientPolynom])>=(m+1))&&(Length[coeficientPolynom][[1]]>=2);*)
     (*Print[Length[pi],"4"];  *)
     beta = -coeficientPolynom[[m + 1, 1]]/
       coeficientPolynom[[1, 1 + 1]];
   	(*Print[Length[pi],"5"];  *)
     tau = {1, 1, m, beta};
     (*Print[tau];*)
     (*Print[Length[pi],"6"];*)
     pi = AppendTo[pi, tau];
     f = (*Collect[*)
       Expand[variables[[1]]^(-m)*(f/.{
            variables[[2]] -> (variables[[1]]^
                tau[[3]]*(tau[[4]] + variables[[2]]))})](*
       variables[[2]]]*);
       (*Print[Length[pi],"7"];*)
       ];
    AppendTo[out, pi];];
   out
   ];

(*puisseaux: for list pi returns the expansion in variables x, y*)
puisseaux[pi_, x_, y_] := Module[{xx=x, yy=y, i},
   (*Print[pi];*)
   For[i = 1, i <= Length[pi], i++, 
    xx = xx /. {x -> pi[[i, 2]]*x^pi[[i, 1]]};
    yy = yy /. {y -> (pi[[i, 4]] + y)*x^pi[[i, 3]], 
       x -> pi[[i, 2]]*x^pi[[i, 1]]};];
   Collect[
   	{Expand[xx], Expand[yy] - Coefficient[yy, y]*y}
   ,x]];
   
(*puisseaux: for list pi returns the expansion in variables x, y*)
puisseaux[pi_, x_, y_, center_] := Module[{xx=x, yy=y, i},
   (*Print[pi];*)
   For[i = 1, i <= Length[pi], i++, 
    xx = xx /. {x -> pi[[i, 2]]*x^pi[[i, 1]]};
    yy = yy /. {y -> (pi[[i, 4]] + y)*x^pi[[i, 3]], 
       x -> pi[[i, 2]]*x^pi[[i, 1]]};];
   Collect[{Expand[xx], -center[[2]]+Expand[yy] - Coefficient[yy, y]*y} /.{ 
        x -> (x - center[[1]])},x]
   ];

Options[PuiseuxExtension] = {Polynomial-> False, Length->3};
PuiseuxExtension[polynomial_, OptionsPattern[]]:=
Module[{singularPart, out, expansion},
singularPart=singular[polynomial, {},{}];
If[OptionValue[Polynomial],
	(*with polynomial*)
	expansion=PuiseuxExpansion[polynomial, Length -> OptionValue[Length]];
	out=Table[{singularPart[[i, 3]],expansion[[i]]}, {i, 1, Length[singularPart]}],
    (*without polynomial*)
    out=Table[singularPart[[i, 3]], {i, 1, Length[singularPart]}]];
out
];

Options[PuiseuxExtensionField] = {Polynomial-> False, Length->3, Extension->False};
PuiseuxExtensionField[polynomial_, OptionsPattern[]]:=
Module[{singularPart, out, expansion},
singularPart=singular[polynomial, {},{}];
If[OptionValue[Polynomial],
	expansion=PuiseuxExpansion[polynomial, Length -> OptionValue[Length]];
	If[OptionValue[Extension],
	(*with polynomial, extension*)
		out=Table[{field[singularPart[[i,3]]],singularPart[[i, 3]],expansion[[i]]},{i, 1, Length[singularPart]}];,
	(*with polynomial, without extension*)
		out=Table[{field[singularPart[[i,3]]],expansion[[i]]},{i, 1, Length[singularPart]}];
	];,
    If[OptionValue[Extension],
    (*without polynomial, with extension*)
		out=Table[{field[singularPart[[i,3]]],singularPart[[i, 3]]},{i, 1, Length[singularPart]}];,
	(*without polynomial, without extension*)
		out=Table[field[singularPart[[i,3]]],{i, 1, Length[singularPart]}];
    ];
];
out
];

field[list_]:=
	Module[{rational, real, fieldString},
		rational=Element[Alternatives@@list,Rationals];
		If[rational,fieldString="Rationals",
			real=Element[Alternatives@@list,Reals];
			fieldString=If[real, "Reals","Complexes"];
		];
		fieldString
	];

Options[PuiseuxExpansion] := {Length -> 6};
PuiseuxExpansion[f_, OptionsPattern[]] := Module[
   {singularPart, expansion, variables, out},
   
   variables = Variables[f];
   
   If[Length[variables]!=2, Message[PuiseuxExpansion::vars, Length[variables]];out=f,	
   (*Print["1"];*)
   (*Check[...,f,Message[]*)
   singularPart = singular[f, {}, {}];
   (*Print["2"];*)
   expansion = regular[singularPart, OptionValue[Length]];
   (*Print["3"];*)
   
   out= Table[Collect[
     puisseaux[expansion[[i]], variables[[1]], variables[[2]]], 
     variables[[1]]], {i, 1, Length[expansion]}]];
   out
   ];

PuiseuxExpansion[f_, center_, OptionsPattern[]] := Module[
   {singularPart, expansion, shiftedPolynom, variables, out},
   variables = Variables[f];
   
   If[Length[variables]!=2, Message[PuiseuxExpansion::vars, Length[variables]];out=f,
   shiftedPolynom = Expand[f/.{variables[[1]] -> (variables[[1]] + center[[1]]), 
   	variables[[2]] -> (variables[[2]] + center[[2]])}];
   singularPart = singular[shiftedPolynom, {}, {}];
   expansion = regular[singularPart, OptionValue[Length]];
   (*Print[expansion];*)
   
   out=Table[Collect[
     Expand[puisseaux[expansion[[i]], variables[[1]], variables[[2]], center]], 
     variables[[1]]], {i, 1, Length[expansion]}]
   ];
   out
   ];

End[]

EndPackage[]

