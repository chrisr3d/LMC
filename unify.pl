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
	ocheck(V,T,A),!.

ocheck(V,T,A) :-
	A==1 -> arg(1,T,X),
	occur_check(V,X);
	arg(A,T,X),
	occur_check(V,X);
	A2 is (A-1),
	ocheck(V,T,A2),!.

check(V,T) :-
	occur_check(V,T),!.

reduit(R, E, P, Q) :-
	.

regle((X ?= T),rename) :-
	var(T),!.

regle((X ?= T),simplify) :-
	atomic(T),!.
	
regle((X ?= T), check) :-
	X \== T,
	occur_check(X,T),!.
	
regle((X ?= T), expand) :-
	compound(T),
	not(occur_check(X,T)),!.
	
regle((S ?= T), decompose) :-
	compound(S), compound(T),
	functor(S,_,A1), functor(T,_,A2),
	A1 == A2,!.
	
regle((T ?= X), orient) :-
	nonvar(T),!.
	
regle((S ?= T), clash) :-
	compound(S), compound(T), functor(S,_,A1), functor(T,_,A2), A1 \== A2,!;
	compound(S), compound(T), functor(S,N1,_), functor(T,N2,_), N1 \== N2,!.
