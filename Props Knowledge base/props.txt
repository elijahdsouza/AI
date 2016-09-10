% props.pl
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% * Adapted in part from rules-swi.pl (original code by Claude Sammut;
%     modified for iProlog by Bill Wilson, October 2001;
%     modified for SWI Prolog by Bill Wilson, April 2006).
% * Translated and extended for sentence parsing by Ben Meadows, August 2013.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/*

 * Top-level commands:
 
 * run.				% Run recognise-act cycles indefinitely.
 * run(X).			% Run as many as X recognise-act cycles.
 * consult(X).		% Load a file X in which commands such as
					%  :- add(Y).  or  :- add_rule(Z).  may be given.
 * add(X).			% Add element X to working memory as a fact.
 * add_rule(X).		% Add rule X to the set of rules in production memory.
 * remove(X).		% Remove all elements matching X from working memory.
 * remove_rule(X).	% Remove all rules with *name* X from production memory.
 
 * wm_trace(all).	% Start tracing all predicates in working memory,
					% printing them to the screen at the end of each cycle.
 * wm_trace.		% Stop tracing any predicates.
 * wm_trace(X).		% Start tracing the pattern X, e.g. wm_trace(buffer(_)).
 * show_wm.			% Shows all the facts in working memory.
 * show_pm.			% Shows all the rules in production memory.
 * run_trace(verbose).	% Prints the full rule instance fired each cycle.
 * run_trace(brief).	% Prints only the rule name each cycle (default).
 * debug_rule(X).	% Explains why a rule with name X can or cannot fire.
 
 * reset.			% Prepares the system to run again, even if e.g.
					% in the middle of a run.
 
 */


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic wm/2. % This allows working memory facts to be asserted.
:- dynamic pm/1. % This allows production memory rules to be asserted.
:- dynamic already_fired/2.
:- dynamic tracked_predicate/1.
:- dynamic cycle_count/1.
:- dynamic glob_cycle_count/1.
:- dynamic recency_counter/1.
:- dynamic debprint/1.
:- dynamic current_nm/2.
:- dynamic elements_to_add_for_instance/1.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% To express rules in a natural way, we define some operators
% First argument to 'op' is the precedence
% Second argument is the associativity (left, right, nonassociative)
% Third argument is the operator name (or list of names)
% This is basically a cosmetic trick to avoid writing the rules as normal
% predicates within nested structures, e.g.
%   if(rule1, then(and(a, and(b, c)), d).
%   if(rule2, then(and(a, b), e).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- op(900, xfx, if).
:- op(800, xfx, then).
:- op(700, xfy, and).

:- op(701, fy, if). % For error handling in incorrectly defined rules;
					% must have greater precedence than 'and'

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

recency_counter(0).

debprint(false).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Prints the contents of memory (we use "wm" to distinguish working memory 
% elements from other entries in Prolog's data base, and "pm" to similarly 
% distinguish rules in production memory)
show_wm :-
	print('--------\nWorking Memory:\n'),
	ignore(
		(wm(Count, X), print('[time '), print(Count), print(']\t* '), print(X), nl, fail)
	),
	nl.

show_pm :-
	print('--------\nProduction Memory:\n'),
	ignore(
		(pm(X), print('* '), print(X), nl, fail)
	),
	nl.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Reset initial working memory
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

reset :-
	retractall(already_fired(_, _)),
		asserta(already_fired(null, false)),
	retractall(glob_cycle_count(_)),
		asserta(glob_cycle_count(0)),
	!.

end :-
	asserta(ended),
	!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Run the recognise-act cycle
% Select a rule, fire it and repeat until no rules are satisfied
% If "fire" succeeds, the cut prevents backtracking
% If "fire" fails, the cycle will repeat
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

run :- run(infinity).
	
run(Cycles) :-
	printcycle2,
	retractall(ended),
	retractall(max_cycle_count(_)),
		asserta(max_cycle_count(Cycles)),
	retractall(cycle_count(_)),
		asserta(cycle_count(0)),
	ignore(run_system_cycle).

run_system_cycle :-
	ended, !.

run_system_cycle :- % Liberal use of cuts to prevent unwanted backtracking
	!,
	cycle_count(X),
	(
		(
			max_cycle_count(infinity),
			Y is 0
		)
		;
		(
			max_cycle_count(MAX),
			(X < MAX),
			Y is (X + 1)
		)
	),
	glob_cycle_count(GX),
	ZX is (GX + 1),
	retractall(cycle_count(_)),
		asserta(cycle_count(Y)),
	retractall(glob_cycle_count(_)),
		asserta(glob_cycle_count(ZX)),
	!,
    select_rule(R),        % Select a single rule for firing
	!,
	(R = [] ;
		(
		printcycle1(R,ZX),
		fire(R),
		printcycle2,
		!,
		ignore(run_system_cycle))
	),
	!.

printcycle1(X, Y) :-
	debprint(true), 
	%print('========\n'), 
	printcycle1_dspace(X, Y).
	%print('========\n').
printcycle1(X, Y) :- 
	debprint(false), 
	%print('========\n'), 
	printcycle1_n(X, Y).
	%print('========\n').

printcycle1_n([],_) :- !.
printcycle1_n((RuleName if _ then _), Cycle) :-
	print('Cycle '), print(Cycle), 
	print(' / '), print(RuleName), nl.

printcycle1_dspace([],_) :- !.
printcycle1_dspace((RuleName if A then B), Cycle) :-
	print('Cycle '), print(Cycle), 
	print(' / '), print(RuleName), nl,
	print('  '), printwithspaces(A), nl,
	print('->'), nl,
	print('  '), printwithspaces(B), nl.

printwithspaces(X and Y) :-
	printwithspaces(X),
	print(' and '),
	printwithspaces(Y),
	!.
printwithspaces(X) :-
	print(X), 
	!.

printcycle1_d([],_) :- !.
printcycle1_d((RuleName if A then B), Cycle) :-
	print('Cycle '), print(Cycle), 
	print(' / '), print(RuleName), nl,
	print('  '), print(A), nl,
	print('->'), nl,
	print('  '), print(B), nl.
	
printcycle2 :-
	print_tracked_predicates,
	print('========\n').

run_trace(verbose) :- retractall(debprint(_)), asserta(debprint(true)).
run_trace(brief) :- retractall(debprint(_)), asserta(debprint(false)).
	
print_tracked_predicates :-
	true,
	ignore(
		(wm(Count, X), tracked_predicate(X), print('[time '), print(Count), print(']\t* '), print(X), nl, fail)
	),
	true.

wm_trace :-
	retractall(tracked_predicate(_)), !.
wm_trace(all) :-
	asserta(tracked_predicate(_)), !.
wm_trace(X) :-
	tracked_predicate(Y),
	Y=X, % Shouldn't be able to have non-universal variables anyway
	!.
wm_trace(X) :-
	asserta(tracked_predicate(X)), !.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% "findall" collects all solutions to "can_fire"
% "resolve" uses some policy to select one of those rules to fire
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

select_rule(SelectedRule) :-
    findall(Rule, can_fire(Rule), Candidates),
    resolve(Candidates, SelectedRule).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Find a rule that hasn't fired before and has its conditions satisfied
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

can_fire(RuleName if Condition then Conclusion) :-
    pm(RuleName if Condition then Conclusion),     % Look up rule in data base
    satisfied(Condition),                      % Are all conditions satisfied?
    not(already_fired(RuleName, Condition)).   % Has it already fired?


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% If pattern is "A and ..." then look for A in working memory and then check 
% the remainder recursively.
%
%    (A and B) = (x and y and z)
%    A = x
%    B = y and Z
%
% If pattern is a single predicate, look it up.
% Note that the cuts "!" prevent a conjunction reaching the simple clauses.
%
% The "check" predicate indicates something that is not a condition to be 
% located in working memory, but a Prolog command to be checked.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

satisfied(check(equal(X,Y)) and B) :- !,
    X = Y,
    satisfied(B).
satisfied(check(equal(X,Y))) :- !,
    X = Y.

satisfied(check(not_equal(X,Y)) and B) :- !,
    X \= Y,
    satisfied(B).
satisfied(check(not_equal(X,Y))) :- !,
    X \= Y.

satisfied(check(is_in(X,Y)) and B) :- !,
    is_in(X,Y),
    satisfied(B).
satisfied(check(is_in(X,Y))) :- !,
    is_in(X,Y).

satisfied(check(is_not_in(X,Y)) and B) :- !,
    not(is_in(X,Y)),
    satisfied(B).
satisfied(check(is_not_in(X,Y))) :- !,
    not(is_in(X,Y)).

satisfied(check(member(X,Y)) and B) :- !,
    member(X, Y),
    satisfied(B).
satisfied(check(member(X,Y))) :- !,
    member(X, Y).

satisfied(check(not_member(X,Y)) and B) :- !,
    not(member(X, Y)),
    satisfied(B).
satisfied(check(not_member(X,Y))) :- !,
    not(member(X, Y)).	

/*
satisfied(check(identical(X,Y)) and B) :- !,
    X == Y,
    satisfied(B).
satisfied(check(identical(X,Y))) :- !,
    X == Y.
	
satisfied(check(not_identical(X,Y)) and B) :- !,
    X \== Y,
    satisfied(B).
satisfied(check(not_identical(X,Y))) :- !,
    X \== Y.
*/

satisfied(A and B) :- !,
    satisfied(A),
    satisfied(B).
satisfied(not(and(A,B))) :- !,
    \+ (wm(_, A), wm(_, B)).
satisfied(not(A)) :- !,
    \+ wm(_, A).
satisfied(A) :- !,
    wm(_, A).

% Recursive member check: Element is a member of [a member of [a...]] List
is_in(Element, List) :-
	member(Element, List).
is_in(Element, List) :-
	member(X, List),
	is_in(Element, X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Conflict resolution strategy: pick the rule with the condition matching the 
% most recent element. In the case of draws, look for next most recent, etc.
% Also check in case no rules were found.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

resolve([], []) :- !.

% Trivial resolution...
% resolve([X|_], X) :- !.

resolve(RuleInstanceList, A) :-
	!,
	member(A, RuleInstanceList),
	\+ (member(B, RuleInstanceList),
		A \== B,
		A = (_NameA if A1 then _A2),
		B = (_NameB if B1 then _B2),
		% Find HIGHEST recency in TimeA
		member_special(A1, TimeA),
			\+ (member_special(A1, TimeA2), TimeA2 > TimeA),
		% Find ANY recency in TimeB
		member_special(B1, TimeB),
		TimeB > TimeA
	).

member_special(X, Time) :-
	% Check conditions OTHER than negated ones
	X = (RecentMember and SomethingElse),
	!,
	(	(RecentMember \= not(_), wm(Time, RecentMember))
		; member_special(SomethingElse, Time)).
	
member_special(RecentMember, Time) :-
	RecentMember \= (_ and _),
	RecentMember \= not(_),
	wm(Time, RecentMember).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Add "already_fired" clause to database so that this particular instantiation
% of the rule is not fired again.
% Add all terms in conclusion to database, if not already there.
% Fail to force backtracking so that a new execution cycle begins.
%
% If there is no rule to fire, succeed. This terminates the execution cycle.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fire(RuleName if Condition then Conclusion) :- !,
    asserta(already_fired(RuleName, Condition)),
	asserta(elements_to_add_for_instance([])),
    process(Conclusion),
	retractall(elements_to_add_for_instance(_)).
fire(_).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% For each term in condition, add it to working memory if not already there.
% 'Remove' retracts something from memory.
% 'Add' asserts something to memory.
% Other predicates (e.g. 'append' in the parser rules) are simply called.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

process(A and B) :-
	!,
    process_element(A),
    process(B).
process(A) :-
    process_element(A),
	elements_to_add_for_instance(List),
	do_final_processing(List).

do_final_processing([]).
do_final_processing([H|T]) :-
	add(H),
	do_final_processing(T).

update_els_to_add(N) :-
	elements_to_add_for_instance(List),
	append([N], List, NewList),
	retractall(elements_to_add_for_instance(_)),
	asserta(elements_to_add_for_instance(NewList)).

process_element(remove(X)) :-
	!, remove(X), !.
process_element(add(X)) :-
	!, update_els_to_add(X), !.
process_element(add_rule(X)) :-
	!, add_rule(X), !.
process_element(X) :-
	X, !.
process_element(X) :-
	(X ; (print('Error! "'), print(X), print('" not a valid rule consequent!\n'), fail)), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Debug a rule.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

debug_rule(Name) :-
	(\+ pm(Name if _ then _)), !,
	print('- - - - -\n'),
	print('No rule of name '), print(Name), print(' found in production memory.\n'),
	print('This rule will not fire.\n'),
	print('- - - - -\n').

debug_rule(Name) :-
	pm(Name if A then B),
	can_fire(Name if A then B),
	( \+  already_fired(Name, A)),
	!,
	print('- - - - -\n'),
	print('Rule of name '), print(Name), print(' is in production memory.\n'),
	print('This rule can fire. Match with working memory elements:\n'),
	print(A), nl,
	print('- - - - -\n').

debug_rule(Name) :-
	pm(Name if A then _),
	!,
	print('- - - - -\n'),
	print('Rule of name '), print(Name), print(' is in production memory.\n'),
	print('This rule can not fire.\n'),
	print('First condition that does not match with any working memory element, in otherwise most successful match:\n'),
	((get_first_nonmatch(A, N),
		print(N), nl) ; true),
	print('- - - - -\n').

get_first_nonmatch(Conditions, Return) :-
	assert(current_nm(-1, foo)),
	ignore(keep_attempting(Conditions, 0)),
	current_nm(_, Return),
	retractall(current_nm(_, _)).
	
keep_attempting(Conditions, CurrentIndex) :-
	(Conditions = (A and B), satisfied(A), I2 is CurrentIndex + 1, keep_attempting(B, I2))
	;
	(Conditions = (A and _), ( \+ satisfied(A)), (update_current_first_nm(CurrentIndex, A), fail))
	;
	(Conditions \= (_ and _), (update_current_first_nm(CurrentIndex, Conditions), fail)).
	
update_current_first_nm(Number, Element) :-
	current_nm(CurNum, _),
	(
		(Number > CurNum)
		-> 
		(retractall(current_nm(_, _)), assert(current_nm(Number, Element)))
		;
		true
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% If term is in memory, don't do anything.
% Otherwise, add new term to memory.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

add_rule(Name if X then Y) :-
	pm(Name if X then Y), !.
add_rule(Name if X then Y) :-
	!, assertz(pm(Name if X then Y)), !.

add_rule(if X then Y) :-
	print('ERROR: Rule syntax not recognised. Rule name missing: \n'),
	print('"if '),
	print(X),
	print(' then '),
	print(Y),
	print('"'),
	!.


add(A) :-
    ground(A),
	wm(X, A), !,
	retractall(wm(X, A)),
	add_at_new_time(A), !.
	
add(A) :-
    ground(A), !, add_at_new_time(A), !.
	
add_at_new_time(A) :-
	recency_counter(T),
	asserta(wm(T,A)),
	retractall(recency_counter(_)),
	T1 is T+1,
	asserta(recency_counter(T1)).

remove(X) :-
	retractall(wm(_,X)),
	remove_fired_records(X),
	!.

remove_rule(X) :-
	retractall(pm(X if _ then _)),
	!.

remove_fired_records(X) :-
	already_fired(RuleName, Condition),
	conditions_contain(Condition, X),
	!,
	%print('RuleName: '), print(RuleName), nl,
	%print('Condition: '), print(Condition), nl,
	%print('X: '), print(X), nl,nl,
	retractall(already_fired(RuleName, Condition)),
	remove_fired_records(X).
	
remove_fired_records(_).

conditions_contain(X, X) :- !.
conditions_contain(X and _, X) :- !.
conditions_contain(_ and X, X) :- !.
conditions_contain(_ and Y, X) :-
	X \= Y,
	conditions_contain(Y, X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Initial directive.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- asserta(glob_cycle_count(0)).


