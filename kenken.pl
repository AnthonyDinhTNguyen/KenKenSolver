%kenken and plain_kenken solutions are based on the mpermutation predicate done
%during discussion by Brett Chalabain
%mpermutaions(Num,L):- length(L,Num), fd_domain(L,1,Num), fd_all_different(L), fd_labeling(L).
%The kenken solver is essentially the same thing but on a 2D array and with an additional constraint from the boxes

    %plain_kenken solution:
    %first constrain T to be a list of Length N, then contrain each element in T to also be a list of length N This makes T a NxN array
    %Next, have prolog try to unify values to each element in T between 1 and N
    %Finally check the assigned values satisfy the operations in each box.
    %Initially, my plain_kenken implementation was very similar to the kenken implementation, except it replaced the finite domain
    %solver with simple predicate replacements, However, this solution was very inefficient as my attempts to implement fd_domain and fd_labeling would waste
    %a lot of time trying solutions that did not fit the kenken format (unique rows and columns). ie. for a 2x2 kenken after it would test [[1,1],[1,1]], it would try [[1,1],[1,2]].
    %Despite the first row [1,1] already being invalid, it would continue altering the second row and testing before backtracking and altering the first row. As the dimentions increased this wasted a lot of time.
    %The way I got around this was by keeping a list for each row to track what values prolog could pick from when unifying the elements to integers.
    %I did the same thing for each column. This saved a lot of time because it ensures that every T that prolog creates has unique rows and columns.
    %Concretely, it ensures that prolog does not waste time binding [[1,1],[1,1]] then [[1,1],[1,2]] then [[1,1],[2,1]]. It just goes straight to creating [[1,2],[2,1]].
    
%This set of predicates creates the Domain, a list from 1-N which we use to determine which values are valid for prolog to pick from when unifying elements in T. This is used for rows in T
domainPredicate(N,Domain):-domainPredicateHelper(N,[],Domain).
domainPredicateHelper(0,List,List):-!.
domainPredicateHelper(N, Res, List):- N>0, NNew is N-1, domainPredicateHelper(NNew,[N|Res], List).

%This set of predicates creates the "vertical domain", or VD. This is a list of N domains, one domain for each column of T. Due to my implementation below, I have to keep the domains for
%the columns all at once in 2D array whereas I have the domains for the rows one at a time in single lists.    
vdInit([],N).
vdInit([H|T],N):- domainPredicate(N,H),vdInit(T,N).
verticalDomain(N,VD):- rightLength(N,VD),forAllRightLength(N,VD),vdInit(VD,N).

%This set of predicates is where prolog starts to unify the elements of T to integers, based on what is valid in the domain for each row and column.    
%The bottom two predicates iterate through each row of T and pass an individual row to the top two predicates.
%The top two predicates iterate through each entry in the row and set it to a value based on what is available the Domain (for Rows) and VD (for columns) entry for that column. 
%It then updates Domain and VD to reflect that other elements that share a row or column can not have the same element as the one prolog bound.    
fromOneToN(N,[T|[]],Domain,[VDhead|[]],[VDres]):-member(T,Domain),member(T,VDhead),delete(VDhead,T,VDres).
fromOneToN(N,[H|Tres],Domain,[VDhead|VDtail],[VDnew|VDres]):-member(H,Domain),member(H,VDhead),delete(Domain,H,NewDomain), delete(VDhead,H,VDnew),  fromOneToN(N,Tres,NewDomain,VDtail,VDres). 
forAll12N(N,[T|[]],Domain,VD,VDnew):- fromOneToN(N,T,Domain,VD,VDnew).    
forAll12N(N,[Head|Tail],Domain,VD,VDnew):-fromOneToN(N,Head,Domain,VD,VDnew), forAll12N(N,Tail,Domain,VDnew,VDnewnew).

%This is used in kenken to turn columns into rows. This makes it easy to reuse predicates that I used to constrain the rows to also constrain each of the columns.
%I initially used this in plain_kenken too, but optimized it out as I tried to improve the performance of plain_kenken.    
getColumns([[]|Z],[]).
    getColumns(M,[X|T]):- getRow(M,X,Ms), getColumns(Ms,T).
    getRow([],[],[]).
    getRow([[X|Xs]|Ys], [X|R], [Xs|Z]) :- getRow(Ys, R, Z).

%Determines length of each element of T    
forAllRightLength(N,[T|[]]):-rightLength(N,T).   
    forAllRightLength(N,[Head|Tail]):- rightLength(N,Head),forAllRightLength(N,Tail).
%makes sure list L has length N    
rightLength(N,L):- length(L,N). 

%Takes the coordinate from form [X|Y] into X and Y vals    
getX([X|_],X).
getY([_|Y],Y).

%Gets X Y values and gets the Value at the X Y Coordinate from T    
getVal(Head,V,T):-getX(Head,X),getY(Head,Y), nth(X,T,R),nth(Y,R,V). 

%matches each of the operations in the boxes and does an appropriate calculation to determine if the are fit the constraint. If not, we backtrack, get new values in T, and try again.
%add multiply and subtract call helper functions explained below.    
fill(_,[]).    
fill(T,+(S,L)):-add(S,L,T,0).
fill(T,*(P,L)):-multiply(P,L,T,1).
    fill(T,-(D,J,K)):-getVal(J,Z,T),getVal(K,B,T),subtr(D,Z,B).
%quotient does caclulation in place since its guarenteed to only do calculation for two values and not a whole list of values. 
fill(T,/(Q,J,K)):-getVal(J,Z,T),getVal(K,B,T),(Z is B*Q;B is Z*Q). %/ put the slash here because emacs was doing something weird with the color of the text

%goes through the list of coordinates. Gets the value at that coordinate from T. Add to accumulator. At the end of list, see if acumulator matches the sum we want     
add(S,[],_,S).
add(S,[Head|Tail],T,Acc):-getVal(Head,V,T),Acc2 is V+Acc, add(S,Tail,T,Acc2). 

%same idea as add except the operation is multiply to the accumulator instead of add to it.     
multiply(P,[],_,P).
multiply(P,[Head|Tail],T,Acc):-getVal(Head,V,T),Acc2 is V*Acc,multiply(P,Tail,T,Acc2).

%guarenteed to only do calculations on two coordinates so it just subtracts them in both directions and then checks if it matches the difference we want.
subtr(D,Z,B):-Res is Z-B,subtractHelper(Res,D).
subtr(D,Z,B):-Res is B-Z,subtractHelper(Res,D).
subtractHelper(A,A).

%goes through all the elements of the C list and does the above calculations on them.     
forAllFill(T,[]).
forAllFill(T,[Head|Tail]):-fill(T,Head),forAllFill(T,Tail).

%create the domain for rows and the vertical domain for columns. Constrain T to be a 2D NxN array. Have prolog start binding values to elements in T. Check if the values fit
%the operations given, if not it backtracks and tries new values then checks those.     
plain_kenken(N,C,T):- domainPredicate(N,Domain), verticalDomain(N,VD),rightLength(N,T), forAllRightLength(N,T), forAll12N(N,T,Domain,VD,VDnew),forAllFill(T,C).    

%kenken solution.
%same idea as the plain_kenken except that this time the finite domain solver     
%sets up the constraints for all the values before prolog goes and labels values.
 

%applies fd_domain to each list in T. fd_domain makes each element in the list have to be between 1 and N
%Then applies fd_all_different to each list in T which makes each list have to have unique items - no duplicates in lists
new12N(N,[T|[]]):-fd_domain(T,1,N).
new12N(N,[H|Tres]):-fd_domain(H,1,N), new12N(N,Tres).     
newForAll12N(N,[T|[]]):-new12N(N,T), fd_all_different(T).
newForAll12N(N,[H|T]):- new12N(N,H), fd_all_different(H),newForAll12N(N,T).

%Same as the one above.
newForAllFill([],T).
newForAllFill([Head|Tail],T):-newFill(Head,T), newForAllFill(Tail,T).

%Same as the one above except in this case instead of using is we use #=.
%#= makes it so the values on the right hand side dont have to necessarily be initialized.
%it just sets up the constraint of what the elements in T have to conform to.
newFill(+(S,L),T):-newAdd(S,L,T,0).
newFill(*(P,L),T):-newMult(P,L,T,1).
newFill(-(D,J,K),T):- getVal(J,Z,T),getVal(K,B,T),(D#=B-Z;D#=Z-B).
newFill(/(Q,J,K),T):-getVal(J,Z,T),getVal(K,B,T),(B #=Z*Q; Z #= B*Q). %/emacs doing weird color things so i put this slash here

newAdd(S,[],_,S).
newAdd(S,[Head|Tail],T,Acc):-getVal(Head,X,T), Snew #= X+Acc,newAdd(S,Tail,T,Snew). 

newMult(S,[],_,S).
newMult(S,[Head|Tail],T,Acc):-getVal(Head,X,T),Snew #= X*Acc,newMult(S,Tail,T,Snew).

%applies fd_labeling to each of the lists in T. This is when prolog goes and binds values to elements in T based on the constraints we have set up using
%the finite domain solver.
forAllLabel([]).
forAllLabel([Head|Tail]):-fd_labeling(Head),forAllLabel(Tail).
kenken(N,C,T):-rightLength(N,T), forAllRightLength(N,T), getColumns(T,Tinv),newForAll12N(N,T), newForAll12N(N,Tinv),newForAllFill(C,T),forAllLabel(Tinv). 

     kenken_testcase(
	 6,
	 [
	  +(11, [[1|1], [2|1]]),
	     /(2, [1|2], [1|3]),
   *(20, [[1|4], [2|4]]),
   *(6, [[1|5], [1|6], [2|6], [3|6]]),
   -(3, [2|2], [2|3]),
	  /(3, [2|5], [3|5]),
	  *(240, [[3|1], [3|2], [4|1], [4|2]]),
	  *(6, [[3|3], [3|4]]),
	  *(6, [[4|3], [5|3]]),
	  +(7, [[4|4], [5|4], [5|5]]),
	  *(30, [[4|5], [4|6]]),
	  *(6, [[5|1], [5|2]]),
	  +(9, [[5|6], [6|6]]),
	  +(8, [[6|1], [6|2], [6|3]]),
	     /(2, [6|4], [6|5]) %/
  ]
).

kenken_testcase_2(
  4,
  [
   +(6, [[1|1], [1|2], [2|1]]),
   *(96, [[1|3], [1|4], [2|2], [2|3], [2|4]]),
   -(1, [3|1], [3|2]),
   -(1, [4|1], [4|2]),
   +(8, [[3|3], [4|3], [4|4]]),
   *(2, [[3|4]])
  ]
).

noop_kenken(N,C,T,Ops):- (T=[[1,2],[2,1]],Ops=[+(3,[[1|1],[2|1]]),-(1,[[1|2],[2|1]])]);(T=[[2,1],[1,2]],Ops=[+(3,[[1|1],[2|1]]),-(1,[[1|2],[2|1]])]).
noop_kenken_testcase(2,[(3,[[1|1],[2|1]]),(1,[[1|2],[2|1]])]).
