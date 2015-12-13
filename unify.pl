:- op(20,xfy,?=).

% Prédicats d'affichage fournis

% set_echo: ce prédicat active l'affichage par le prédicat echo
set_echo :- assert(echo_on).

% clr_echo: ce prédicat inhibe l'affichage par le prédicat echo
clr_echo :- retractall(echo_on).

% echo(T): si le flag echo_on est positionné, echo(T) affiche le terme T
%          sinon, echo(T) réussit simplement en ne faisant rien.

echo(T) :- echo_on, !, write(T).
echo(_).


print(Term) :-
	current_prolog_flag(print_write_options, Options), !,
	write_term(Term, Options).


/* occur_check(V,T) permet de vérifier si la variable V est contenue dans le terme T */

occur_check(V,T) :- V==T -> !; compound(T), functor(T,N,A), ocheck(V,T,A),!.

ocheck(V,T,A) :- A==1 -> arg(1,T,X), occur_check(V,X); arg(A,T,X), occur_check(V,X); A2 is (A-1), ocheck(V,T,A2),!.

% Rappel : E = Equation. R = Règle de transformation. P = Système d'équations. Q = Système d'équation
% Unifie(P,S) où S = choix_premier

/* regle(E,R) : Détermine la règle de transformation R qui peut s'appliquer à l'équation E. */

regle((X ?= T), clash) :- compound(X), compound(T), functor(X,_,N1), functor(T,_,N2), N1 \== N2,!;
        compound(X), compound(T), functor(X,A1,_), functor(T,A2,_), A1 \== A2,!.

regle((X ?= T),rename) :- var(X), var(T),!.

regle((X ?= T),simplify) :- var(X), atomic(T),!.

regle((X ?= T), check) :- X \== T, occur_check(X,T),!.

regle((X ?= T), expand) :- var(X), compound(T), not(occur_check(X,T)),!.

regle((X ?= T), decompose) :- compound(X), compound(T), functor(X,A1,N1), functor(T,A2,N2), A1 == A2, N1 == N2,!.

regle((T ?= X), orient) :- nonvar(T), var(X),!.


/* reduit(R,E,P,Q) : Transforme le système d'équations P en le système d'équations Q par application de la règle de transformation R à l'équation E.*/

reduit(R,(X ?= T),P,Q,P1,Q1) :- R==rename, echo(system  : [X ?= T|P]), nl, echo(R : X ?= T),
										nl, substitution(X,T,P,P1), Q1=[X=T|Q2], substitution2(X,T,Q,Q2), !.

reduit(R,(X ?= T),P,Q,P1,Q1) :- R==simplify, echo(system  : [X ?= T|P]), nl, echo(R : X ?= T),
										nl, substitution(X,T,P,P1), Q1=[X=T|Q2], substitution2(X,T,Q,Q2), !.

reduit(R,(X ?= T),P,Q,P,Q) :- R==check, echo(system : [X ?= T|P]), nl, echo(R : X ?= T), nl, fail, !.

reduit(R,(X ?= T),P,Q,P1,Q1) :- R==expand, echo(system  : [X ?= T|P]), nl, echo(R : X ?= T), nl,
										substitution(X,T,P,P1), Q1=[X=T|Q2], substitution2(X,T,Q,Q2), !.

reduit(R, (X ?= T),P,Q,[T ?= X|P],Q) :- R==orient, echo(system  : [X ?= T|P]), nl, echo(R : X ?= T), nl, !.

reduit(R,(X ?= T),P,Q,P1,Q) :- R==decompose, echo(system  : [X ?= T|P]), nl, echo(R : X ?= T), nl,
										functor(X,_,A), liste_arguments((X ?= T),A,[],L), concat(L,P,P1), !.

reduit(R,(X ?= T),P,Q,P,Q) :- R==clash, echo(system : [X ?= T|P]), nl, echo(R : X ?= T), nl, fail, !.



substitution(_,_,[],[]) :- !.
substitution(X,T,[A ?= B|P],[A2 ?= B2|P2]) :- substitution_terme(X,T,A,A2), substitution_terme(X,T,B,B2),
												substitution(X,T,P,P2).
substitution2(_,_,[],[]) :- !.
substitution2(X,T,[A ?= B|P],[A2 ?= B2|P2]) :- substitution_terme(X,T,A,A2), substitution_terme(X,T,B,B2),
												substitution2(X,T,P,P2).
substitution_terme(X,T,A,T) :- not(compound(A)), A==X,!.
substitution_terme(X,T,A,A) :- not(compound(A)), A\==X,!.
substitution_terme(X,T,A,A2) :- compound(A), functor(A,_,NA), substitution_argument(X,T,A,NA,A2),!.
substitution_argument(X,T,A,N,A2) :- N==1 -> functor(A,NM,AR), arg(1,A,VA), substitution_terme(X,T,VA,V), functor(A2,NM,AR), arg(1,A2,V),!;
									functor(A,NM,AR), arg(N,A,VA), substitution_terme(X,T,VA,V), functor(A2,NM,AR), arg(N,A2,V), N2 is (N-1), substitution_argument(X,T,A,N2,A2).


liste_arguments((X ?= T),N,L,L2) :- N==1 -> arg(1,X,A), arg(1,T,B), L2=[A ?= B|L],! ;
									N2 is (N-1), arg(N,X,A), arg(N,T,B), liste_arguments(A ?= B,N2,[A ?= B|L],L2).

concat([],X,X).
concat([X|Q],Y,[X|P]) :- concat(Q,Y,P).



unifieRes([],Q) :- nl, print(Q),!.
unifieRes([X|P],Q) :- regle(X,R), reduit(R,X,P,Q,P1,Q1), unifieRes(P1,Q1).
unifie([]) :- !.
unifie([X|P]) :- set_echo, regle(X,R), reduit(R,X,P,[],P1,Q1), unifieRes(P1,Q1).
