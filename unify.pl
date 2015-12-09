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

% reduit(R,E,P,Q) :
%	Transforme le système d'équations P en le système d'équations Q par application de la règle de transformation R à l'équation E.
reduit(R, E, P, Q) :- 
	.

% regle(E,R) : 
%	Détermine la règle de transformation R qui s'applique à l'équation E.

% La règle Rename peut être appliquée à l'équation X = T si T est une variable.
regle((X ?= T),rename) :-
	var(T),!.

% La règle Simplify peut être appliquée à l'équation X = T si T est une constante.
regle((X ?= T),simplify) :-
	atomic(T),!.

% Check est la règle qui intervient au niveau de l'équation X = T si X est différent de T et que X apparaît dans T
regle((X ?= T), check) :-
	X \== T,
	occur_check(X,T),!.

% La règle Expand s'applique à l'équation X = T si T est composé et que X n'apparaît pas dans T
regle((X ?= T), expand) :-
	compound(T),
	not(occur_check(X,T)),!.

% On peut décomposer une équation S = T lorsque S et T sont composés, et que S et T ont le même nombre d'arguments
regle((S ?= T), decompose) :-
	compound(S), compound(T),
	functor(S,_,A1), functor(T,_,A2),
	A1 == A2,!.

% La règle Orient est applicable à l'équation T = X lorsque T n'est pas une variable.
regle((T ?= X), orient) :-
	nonvar(T),!.

% La règle Clash est applicable à l'équation S = T lorsque S et T sont composés, et que soit S et T n'ont pas le même nombre d'arguments, soit n'ont pas le même nom.
regle((S ?= T), clash) :-
	compound(S), compound(T), functor(S,_,N1), functor(T,_,N2), N1 \== N2,!;
	compound(S), compound(T), functor(S,A1,_), functor(T,A2,_), A1 \== A2,!.
