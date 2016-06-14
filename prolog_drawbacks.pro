% Luster and poverty of Prolog
% Illustration of the best points of Prolog and its drawbacks.

% The append relation succinctly shows what is best in Prolog.

append([],L,L).
append([H|T],L,[H|L2]) :- append(T,L,L2).

% It is tempting to read these two lines algorithmically:
% to append the empty list to L, return L, etc.
% But such an reading will be misleading (in bigger cases).
%
% We should read these two lines _declaratively_:
% logically or relationally.
% The two append lines define the first-order theory for
% append: 
%   -- the 3-place predicate append,
%   -- an axiom: forall L. append([],L,L) holds.
%   -- a rule: forall H T L L2.
%       whenever append(T,L,L2) holds,
%       append([H|T],L,[H|L2]) also holds.
%       (that is, we can add an element to T and L2).
% Capitalized names: logic variables, implicitly quantified.
%
% There is no distinction between input and output, arguments and
% result.

% We can ask Prolog:
% Is it true that there exists a list L such that
?- append([1,2],[3,4,5],L).
% holds?
% This looks like computing the concatenation of two lists.
%
% But we can also ask
% is it true that there exists L such that
?- append([1,2],L,[1,2,3,4,5]).
% If list concatenation was like running forwards, prefix
% removal is like running backwards.
%
% we can also ask
?- append(L1,L2,[1,2,3,4,5]).
% if a list [1,2,3,4,5] can be split into a prefix and the suffix.
% The splitting is non-deterministic. Prolog can enumerate
% all the possible ways.


% The second example: palindrome.
% What is a palindrome? The following is almost the English definition:

pali([]).
pali(['a']).
pali(['b']).
pali(['a'|T]) :- append(L,['a'],T), pali(L).
pali(['b'|T]) :- append(L,['b'],T), pali(L).

%% We can add weights.

% recognizing
?- pali(['a','b','a']).
% generating
?- pali(L).

lenbad([],0).
lenbad([_|T],N) :- lenbad(T,N-1).

% Why not lenbad(T,eval(N-1)).

%% ?- lenbad(X,3).

lenb([],0).
lenb([_|T],N) :- N1 is N-1, lenb(T,N1).


lenf([],0).
lenf([_|T],N) :- lenf(T,N1), N is N1 + 1.

lenf1([],0).
lenf1([_|T],N) :- N is N1 + 1, lenf1(T,N1).

% We use FFI (arithmetic) but standard libraries are
% usually deterministic, and arithmetic is functional
% rather than relational.
% Solutions: constraints, in Kanren.

?- pali(X), lenb(X,5).

%% Conditioning
% looping

?- lenb([1],N).
% A run-time error (after perhaps spending long time....).

bool(t).
bool(f).

boollist([]).
boollist([H|T]) :- bool(H), boollist(T).

?- append([f,f],X,R), boollist(X), boollist(R).


% Zebra in Prolog.

% Parsing
digit(0).
digit(1).
digit(2).
digit(3).
digit(4).
digit(5).
digit(6).
digit(7).
digit(8).
digit(9).

numr([],[]) :- print('eof'), fail.
numr([D|S],R) :- digit(D), numr_many0(S,R).
numr_many0(S,S).
numr_many0([D|S],R) :- digit(D), numr_many0(S,R).

tel(S,R) :- numr(S,[-|S1]),numr(S1,[-|S2]),numr(S2,R).
tel(S,R) :- numr(S,[-|S1]),numr(S1,R]).

% ------------------------------------------------------------------------
% The database example
db1([rec(name('山下'),graduated(no),grades([4,4]))]).

db2([rec(name('山下'),graduated(no),grades([4,4])),
     rec(name('山田'),graduated(yes),grades([2,3,4,4]))]).

db3([rec(name('山下'),graduated(no),grades([4,4])),
     rec(name('田中'),graduated(yes),grades([4,4]))]).

% delete a graduated student from the database and prints its data.
% Say 'none graduated' if the record has no graduated students.

print_rec(rec(name(N),graduated(yes),grades([G1,G2,G3,G4]))) :-
    print('Student: '),print(N),print(' Grades:'),
    print(G1),print(', '),
    print(G2),print(', '),
    print(G3),print(', '),
    print(G4),nl.

% almost like append
del_rec([Rec|LRem],Rec,LRem) :- 
    Rec = rec(name(_),graduated(yes),grades(_)).
del_rec([H|T],Rec,[H|LRem]) :- del_rec(T,Rec,LRem).

% subtle difference: print 'none graduated' if cannot delete and cannot print.

prog1(Db) :- del_rec(Db,R,DbRem), print_rec(R), nl, print(DbRem).
prog1(_) :- print('None graduated').

?- db1(X), prog1(X).

prog2(Db) :- del_rec(Db,R,DbRem) -> print_rec(R), nl, print(DbRem);
             print('None graduated').
?- db1(X), prog2(X).
?- db2(X), prog2(X).
?- db3(X), prog2(X).
% Now gives false.

?- db2(X), prog1(X).
%% Student: 山田 Grades:2, 3, 4, 4

%% [rec(name(山下),graduated(no),grades([4,4]))]
%% X = [rec(name(山下), graduated(no), grades([4, 4])), rec(name(山田), graduated(yes), grades([2, 3, 4, 4]))] ;
%% None graduated
%% X = [rec(name(山下), graduated(no), grades([4, 4])), rec(name(山田), graduated(yes), grades([2, 3, 4, 4]))].

?- db2(X), prog2(X).
%% Student: 山田 Grades:2, 3, 4, 4

%% [rec(name(山下),graduated(no),grades([4,4]))]
%% X = [rec(name(山下), graduated(no), grades([4, 4])), rec(name(山田), graduated(yes), grades([2, 3, 4, 4]))].

?- db3(X), prog1(X).
%% None graduated
%% X = [rec(name(山下), graduated(no), grades([4, 4])), rec(name(田中), graduated(yes), grades([4, 4]))].

?- db3(X), prog2(X).
%% false.

% Problems with committed choice
% simpler deletion

del([H|T],H,T).
del([H|T],D,[H|R]) :- del(T,D,R).

prog1(L,S) :- (del(L,true,LRem), S=deleted(LRem));
              S=failed.

%% ?- prog1([false,true,false],S).
%% S = deleted([false, false]) ;
%% S = failed.

%% ?- prog1(L,S).
%% L = [true|_G16],
%% S = deleted(_G16) ;
%% L = [_G15, true|_G19],
%% S = deleted([_G15|_G19]) ;
%% L = [_G15, _G21, true|_G25],
%% S = deleted([_G15, _G21|_G25]) ;
%% L = [_G15, _G21, _G27, true|_G31],
%% S = deleted([_G15, _G21, _G27|_G31]) 

prog3(L,S) :- del(L,true,LRem) -> S=deleted(LRem); S=failed.

%% ?- prog3([true,false,true],S).
%% S = deleted([false, true]).

%% ?- prog3(L,S).
%% L = [true|_G16],
%% S = deleted(_G16).

%% ?- prog3([false,false,true,false],S).
%% S = deleted([false, false, false]).

delc([H|T],H,T).
delc([H|T],D,[H|R]) :- H #\= D, delc(T,D,R).

prog4(L,S) :- delc(L,1,Rem) -> S=deleted(Rem); S=failed.

delc1([H|T],H,T).
delc1([H|T],D,R) :- H #\= D, delc1(T,D,R).

prog5(L,S) :- delc1(L,1,Rem) -> S=deleted(Rem); S=failed.
