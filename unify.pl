:- op(20, xfy, [?=]).

print(Term) :-
	current_prolog_flag(print_write_options, Options), !, 
	write_term(Term, Options).

unifie(P) :-
	reduit(_, _, P, Q),
	print(Q).

decompose(E) :-
	compound_name_arity(E, ?=, _),
	arg(1, E, X),
	arg(2, E, Y),
	compound_name_arity(X, Z, A),
	compound_name_arity(Y, Z, A).

decompose(E, P, Q) :-
	print(E),
	union(E, K, P),
	print(K),
	arg(1, E, I),
	arg(2, E, J),
	arg(N, I, L),
	arg(N, J, D),
	
	union([L ?= I], K, Q).

occur_check(V,T) :-
	V==T -> !;
	compound(T),
	functor(T,N,A),
	check(V,T,A),!
	%arg(_,T,Z),
	%V==Z.
.

check(V,T,A) :-
	A==1 -> arg(1,T,X),
	occur_check(V,X);
	arg(A,T,X),
	occur_check(V,X);
	A2 is (A-1),
	check(V,T,A2),!
.

reduit(R, E, P, Q) :-
	.

regle((A ?= B),rename) :-
	var(B),!.

regle((A ?= B),simplify) :-
	atomic(B),! .
