% ===========================================================
% Main loop:
% 1. Repeat "input-response" cycle until input starts with "bye"
%    Each "input-response" cycle consists of:
% 		1.1 Reading an input string and convert it to a tokenized list
% 		1.2 Processing tokenized list
% ===========================================================
%parse([every,white,container,on,the,bottom,shelf,contains,a,banana],X).
chat:-
 repeat,
   readinput(Input),
   process(Input),
  (Input = [bye| _] ),!.


% ===========================================================
% Read input:
% 1. Read char string from keyboard.
% 2. Convert char string to atom char list.
% 3. Convert char list to lower case.
% 4. Tokenize (based on spaces).
% ===========================================================

readinput(TokenList):-
   read_line_to_codes(user_input,InputString),
   string_to_atom(InputString,CharList),
   string_lower(CharList,LoweredCharList),
   tokenize_atom(LoweredCharList,TokenList).


% ===========================================================
%  Process tokenized input
% 1. Parse morphology and syntax, to obtain semantic representation
% 2. Evaluate input in the model
% If input starts with "bye" terminate.
% ===========================================================

process(Input):-
	parse(Input,SemanticRepresentation),
	modelchecker(SemanticRepresentation,Evaluation),
	respond(Evaluation),!,
	nl,nl.

process([bye|_]):-
   write('> bye!').


% ===========================================================
%  Parse:
% 1. Morphologically parse each token and tag it.
% 2. Add semantic representation to each tagged token
% 3. Obtain FOL representation for input sentence
% ===========================================================

parse(Input, SemanticRepresentation):- sr_parse(Input).

sr_parse([]).
sr_parse(Sentence):-
        srparse([],Sentence).

srparse([X],[]):-
  numbervars(X,0,_),
  write(X).

srparse([Z,Y,X|MoreStack],Words):-
       rule(LHS,[X,Y,Z]),
       srparse([LHS|MoreStack],Words).

srparse([Y,X|MoreStack],Words):-
       rule(LHS,[X,Y]),
       srparse([LHS|MoreStack],Words).

srparse([X|MoreStack],Words):-
       rule(LHS,[X]),
       srparse([LHS|MoreStack],Words).

srparse(Stack,[Word|Words]):-
        lex(X,Word),
        srparse([X|Stack],Words).


% ===========================================================
% Grammar
% 1. List of lemmas
% 2. Lexical items
% 3. Phrasal rules
% ===========================================================

%Every white container on the bottom shelf [tv inf contains [dt a [n banana]]]


% --------------------------------------------------------------------
% Lemmas are uninflected, except for irregular inflection
% lemma(+Lemma,+Category)
% --------------------------------------------------------------------

lemma(a,dtexists).
lemma(an,dtexists).
lemma(some,dtexists).

lemma(the,dt).
lemma(no,dt).

lemma(each,dtforall).
lemma(all,dtforall).
lemma(every,dtforall).

lemma(burger,n).
lemma(ham,n).
lemma(almond,n).
lemma(box,n).
lemma(banana,n).
lemma(bowl,n).
lemma(container,n).
lemma(egg,n).
lemma(freezer,n).
lemma(fridge,n).
lemma(meat,n).
lemma(milk,n).
lemma(popsicles,n).
lemma(sandwich,n).
lemma(shelf,n).
lemma(watermelon,n).

lemma(tom,pn).
lemma(jose,pn).
lemma(sue,pn).
lemma(alba,pn).
lemma(john,pn).
lemma(mia,pn).
lemma(sam,pn).

lemma(almond,adj).
lemma(empty,adj).
lemma(red,adj).
lemma(green,adj).
lemma(blue,adj).
lemma(white,adj).
lemma(top,adj).
lemma(bottom,adj).
lemma(middle,adj).
lemma(yellow,adj).

lemma(is,be).
lemma(was,be).
lemma(are,be).

lemma(eat,tv).
lemma(ate,tv).
lemma(drink,tv).
lemma(drank,tv).
lemma(drunk,tv).
lemma(drinks,tv).
lemma(contain,tv).


lemma(has,tv).
lemma(had,tv).
lemma(have,tv).

lemma(belongs,pv).
lemma(rely,pv).

lemma(did,aux).
lemma(does,aux).

lemma(put,dtv).
lemma(puts,dtv).

lemma(that,rel).
% WH questions vs REL, how to figure ambiguity/
% lemma(who,rel).
% lemma(what,rel).
% lemma(which,rel).

lemma(in,p).
lemma(under,p).
lemma(below,p).
lemma(inside,p).

lemma(on,vacp).
lemma(to,vacp).
lemma(there,vacp).


lemma(who,whpr).
lemma(which,whpr).
lemma(what,whpr).


lemma(Word,Tag,Stem) :- atom_chars(Word, WordList),
                   lemma(Stem,Tag),
                   atom_chars(Stem, LemmaList),
                   compare_lemma(WordList,LemmaList),!.

compare_lemma(_,[]).
compare_lemma([W|WordList],[W|LemmaList]) :-
                  compare_lemma(WordList,LemmaList).
% --------------------------------------------------------------------
% Constructing lexical items:
% word = lemma + suffix (for "suffix" of size 0 or bigger)
% --------------------------------------------------------------------

%[every blue container on the top shelf contains a sandwich that has no meat]
%[every white container on the bottom shelf contains a banana] (works)
% [a,blue,box,contains,ham]
% [a,blue,box,contains,some,ham]
% [the,white,box,that,the,freezer,contains,belongs,to,sue]
% is,there,an,egg,inside,the,blue,box
% are,there,two,eggs,inside,the,blue,box
% what,does,the,green,box,contain
% who,put,every,yellow,box,on,the,white,bowl

%lex(X,tom).
lex(pn( (P)^X ),Word):-
    lemma(Word,pn),
    P=..[^,Word,X].

%lex(X,blue)
lex(adj((X^P)^X^and(P,Q)),Word):-
  	lemma(Word,adj),
    Q =.. [Word,X].

%rc(), n(_4686^meat(_4686))

%sr_parse([what,does,the,green,box,contain])
%lex(A,what), lex(B,does),lex(C,the), lex(D,green), lex(E,box), lex(F,contain),
%rule(P,[D,E]), rule(Q,[C,P]), rule(R,[F]), rule(S,[R]).


%sr_parse([tom,put,a,box,on,the,bowl])


lex(dt((X^P)^(X^Q)^exists(X,(and(P,Q)))),Word):-
  	lemma(Word,dtexists).

%lex(X,that).
lex(rel([]), Word):- lemma(Word,rel).

lex(dt((X^P)^(X^Q)^Z),Word):-
   lemma(Word,dt),
    A = and(P,Q),
    Z =..[Word,X,A].

%lex(X,on)

lex(vacp([]),Word) :-
  lemma(Word,vacp).

lex(p((Y^Z)^Q^(X^P)^and(P,Q)),Word) :-
  lemma(Word,p),
  Z =.. [Word,X,Y].

%lex(tv(X^Y^Z,[]), Word):-
%      lemma(Word,tv),
%      Z =..[Word,X,Y].

%lex(n(X^P),Word):-
%	lemma(Word,n),
%	P=.. [Word,X].

lex(X, Word):-
      lemma(Word,aux),
      X = aux.

lex(X, Word):-
      lemma(Word,be),
      X = be.

lex(whpr((X^Y)^P),Word) :- lemma(Word,whpr), P=..[Word,X,Y].

lex(dt((X^P)^(X^Q)^forall(X,imp(P,Q))),Word):-
		lemma(Word,dtforall).

%Last resource is to stem the word
%Stemming for verb
lex(tv(X^Y^Z,[]), Lemma):-
      lemma(Lemma,tv,Stem),
      Z =..[Stem,Y,X].

lex(pv(X^Y^Z,[]), Lemma):-
      lemma(Lemma,pv,Stem),
      Z =..[Stem,Y,X].

lex(dtv(W^X^Y^Z,[]), Lemma):-
      lemma(Lemma,dtv,Stem),
      Z =..[Stem,W,X,Y].



%Stemming for noun
%lex(X,egg)
lex(n(X^P),Lemma):-
	lemma(Lemma,n,Stem),
	P=.. [Stem,X].


% (X^Q)^exists(X,and(egg(X),Q))

% --------------------------------------------------------------------
% Suffix types
% --------------------------------------------------------------------

% ...

% --------------------------------------------------------------------
% Phrasal rules
% rule(+LHS,+ListOfRHS)
% --------------------------------------------------------------------

%sr_parse([the,white,box,that,the,freezer,contains,belongs,to,sue]).

% lex(A,the),lex(B,white),lex(C,box),lex(D,that),lex(E,the),
% lex(F,freezer),lex(G,contains),lex(H,belongs),lex(I,to),lex(J,sue),
% rule(K,[J]), rule(L,[H,I]), rule(M,[G]),.

%sr_parse([is,there,an,egg,inside,the,blue,box]).



%sr_parse([tom,put,a,box,on,the,bowl])
% lex(A,tom), lex(B,put),
% lex(C,a), lex(D,box),
% lex(E,on), lex(F,the), lex(G,bowl),
% rule(H,[A]), rule(I,[C,D]), rule(J,[F,G]), rule(K,[E,J]),
% rule(X,[B,I,K])., rule(S,[H,X]).

% B = dtv(A^F^G^put(A, F, G), []),
% I = np(    (F^G) ^exists(F, and(box(F), G)) ),
% K = pp(    (F^G) ^the(F, and(bowl(F), G)))

%rule(vp(X^K,[]),[dtv(X^A^K,[]),np(A),pp(A^C)]).

%rule(vp(X^K,[]),[tv(X^Y,[]),np(Y^K)]).
%np(X^Y),pp((X^Y)^Z)

%RC -> REL VP
rule(rc(X,[]),[rel([]),vp(X,[])]).

rule(n(X^and(Y,Z)),[n(X^Y),rc(Z,[X])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(X^Z,[])]).

% NP -> DT N
rule(np(Y),[dt(X^Y),n(X)]).
% NP ->N
rule(np((X^Q)^exists(X,and(P,Q))),[n(X^P)]).

% N -> N PP
rule(n(X^Z),[n(X^Y),pp((X^Y)^Z)]).
% N -> Adj N
rule(n(Y),[adj(X^Y),n(X)]).

%rule(n(X),[vacp([]),n(X)]).

% NP -> PN
rule(np(X),[pn(X)]).
% PP -> P NP
rule(pp(Z),[p(X^Y^Z),np(X^Y)]).
% PP -> vacp NP
rule(pp(X^Y),[vacp([]),np(X^Y)]).
% VP -> IV
rule(vp(X,[]),[iv(X,[])]).
% VP -> TV NP
%rule(vp(X^W),[tv(X^Y),np(Y^W)]).
rule(vp(X^K,[]),[tv(X^Y,[]),np(Y^K)]).

% IV -> TV
rule(iv(Y,[X]),[tv(X^Y,[])]).

%lex(A,who),lex(B,did),lex(C,john),lex(D,rely),lex(E,on), rule(F,[D,E]).
% lex(A,who),lex(B,did),lex(C,john),lex(D,rely),lex(E,on),
% rule(F,[D,E]), rule(G,[C]), rule(H,[G,F]).

% lex(A,is),lex(B,there),lex(C,an), lex(D,egg), lex(E,inside),lex(F,the),lex(G,blue),
% lex(H,box), rule(P,[G,H]), rule(Q,[F,P]), rule(R,[E,Q]), rule(S,[C,D]),
% rule(T,[B,S]), rule(U,[A,T,R]).

rule(vp(X,[]),[pv(X,[]),vacp(_)]).


%New Question rules
rule(vp(K,[WH]),[tv(Y,[WH]),np(Y^K)]).
rule(vp(X,WH),[iv(X,WH)]).
rule(s(X,[WH]),[vp(X,[WH])]).

% WH QUESTIONS rules
rule(Y,[whpr(X^Y),vp(X,[])]).

rule(Z,[whpr(Y^Z), ynq(Y)]).

rule(ynq(Y),[aux, np(X^Y),vp(X,[])]).

rule(ynq(Z),[be, np(X^Y),pp((X^Y)^Z)]).

rule(Z,[whpr((X^Y)^Z), inv_s(Y,[X])]).
%S -> AUX NP VP
rule(inv_s(Y,[WH]),[aux, np(X^Y),vp(X,[WH])]).

%Transform What into Q
rule(q(A,and(thing(A),X)),[what(A,X)]).
rule(q(A,and(person(A),X)),[who(A,X)]).


%rule(q(A,and(thing(A),X)),[who(A,rely(john,B))]).


%rule(vp(X^W),[tv(X^Y),n(Y^W)]).

% VP -> DTV NP NP eg: I gave Sue a burger

% VP -> DTV NP PP eg: sam put every yellow box on the white bowl

% sr_parse([tom,put,a,box,on,the,bowl])

%lex(W,tom), lex(X,eat), lex(Y,a), lex(Z,burger).

% dtv(W^A^B^ put(W,X,Y), []).
% np( (A^B) ^the(A,and(burger(A),B)))
% pp( (A^B) ^ and(B,the(C,and(and(box(C),white(C)),on(A,C)))) )




% VP -> VP PP eg: The top shelf contains eggs in a box
% VP -> SV S eg:
% VP -> ADV VP eg:
% VP -> AUX VP eg:
% DT -> NP POS do we need to handle this? POS->s eg: The upper shelf contains Sam's box

% S -> NP VP eg: The white container contains egg


% ===========================================================
%  Modelchecker:
%  1. If input is a declarative, check if true
%  2. If input is a yes-no question, check if true
%  3. If input is a content question, find answer
% ===========================================================

% model(...,...)
rule(s(Y),[np(X^Y),vp(X,_)]).

% ===========================================================
%  Respond
%  For each input type, react appropriately.
% ===========================================================

% Declarative true in the model
respond(Evaluation) :-
		Evaluation = [true_in_the_model],
		write('That is correct'),!.

% Declarative false in the model
respond(Evaluation) :-
		Evaluation = [not_true_in_the_model],
		write('That is not correct'),!.

% Yes-No interrogative true in the model
respond(Evaluation) :-
		Evaluation = [yes_to_question],
		write('yes').

% Yes-No interrogative false in the model
respond(Evaluation) :-
		Evaluation = [no_to_question],
		write('no').

% wh-interrogative true in the model
% ...

% wh-interrogative false in the model
% ...

%s(forall(A,imp(and(and(container(A),blue(A)),exists(B,and(and(shelf(B),top(B)),on(A,B)))),
%and(exists(C,and(sandwich(C),contains(A,C))),meat(D^has(C^contains(A,C),D)))))).
