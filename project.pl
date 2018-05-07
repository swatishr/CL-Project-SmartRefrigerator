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

lemma(ham,n).
lemma(almond,n).
lemma(box,n).
lemma(banana,n).
lemma(bowl,n).
lemma(container,n).
lemma(freezer,n).
lemma(fridge,n).
lemma(meat,n).
lemma(milk,n).
lemma(popsicles,n).
lemma(sandwich,n).
lemma(shelf,n).
lemma(watermelon,n).

lemma(tom,pn).
lemma(mia,pn).
lemma(sam,pn).

lemma(almond,adj).
lemma(empty,adj).
lemma(red,adj).
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
lemma(contains,tv).

lemma(has,tv).
lemma(had,tv).
lemma(have,tv).

lemma(did,aux).

lemma(that,rel).
% WH questions vs REL, how to figure ambiguity/
% lemma(who,rel).
% lemma(what,rel).
% lemma(which,rel).

lemma(in,p).
lemma(under,p).
lemma(below,p).
lemma(on,vacp).
lemma(to,vacp).

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
% a,blue,box,contains,ham
% a,blue,box,contains,some,ham (works)
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


%lex(X,the).
lex(dt((X^P)^(X^Q)^exists(X,(and(P,Q)))),Word):-
  	lemma(Word,dtexists).

%lex(X,that).
lex(rel([]), Word):- lemma(Word,rel).

lex(dt((X^P)^(X^Q)^Z),Word):-
   lemma(Word,dt),
    A = and(P,Q),
    Z =..[Word,X,A].

%lex(X,on)
%vacp((Y^on(X,Y))^Q^(X^P)^and(P,Q))
%vacp((Y^on(X,Y))^Q^(X^P)^and(P,Q))
lex(vacp((Y^Z)^Q^(X^P)^and(P,Q)),Word) :-
  lemma(Word,vacp),
  Z =.. [Word,X,Y].

lex(tv(X^Y^Z,[]), Word):-
      lemma(Word,tv),
      Z =..[Word,X,Y].

lex(X, Word):-
      lemma(Word,aux),
      X = aux.

lex(whpr(X^P),Word) :- lemma(Word,whpr), P=..[Word,X].

lex(dt((X^P)^(X^Q)^forall(X,imp(P,Q))),Word):-
		lemma(Word,dtforall).

%Last resource is to stem the word
lex(n(X^P),Lemma):-
	lemma(Lemma,n,Stem),
	P=.. [Stem,X].

% ...

% --------------------------------------------------------------------
% Suffix types
% --------------------------------------------------------------------

% ...

% --------------------------------------------------------------------
% Phrasal rules
% rule(+LHS,+ListOfRHS)
% --------------------------------------------------------------------

rule(rc(X,[]),[rel([]),vp(X,[])]).

rule(n(X^and(Y,Z)),[n(X^Y),rc(Z,[X])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(X^Z,[])]).
%rule(n(X^and(Y,Z)),[n(X^Y),rc(X^Z,[])]).

% NP -> DT N
rule(np(Y),[dt(X^Y),n(X)]).
% NP ->N
rule(np(X),[n(X)]).
% N -> N PP
rule(n(X^Z),[n(X^Y),pp((X^Y)^Z)]).
%NP -> NP PP
rule(np(Z),[np(X^Y),pp((X^Y)^Z)]).

% N -> Adj N
rule(n(Y),[adj(X^Y),n(X)]).
% NP -> PN
rule(np(X),[pn(X)]).
% NP -> PRP
rule(np(X),[prp(X)]).
% PP -> P NP
rule(pp(Z),[p(X^Y^Z),np(X^Y)]).

% PP -> vacp NP
rule(pp(Z),[vacp(X^Y^Z),np(X^Y)]).

% VP -> IV
rule(vp(X,[]),[iv(X)]).
% VP -> TV NP
%rule(vp(X^W),[tv(X^Y),np(Y^W)]).
rule(vp(X^K,[]),[tv(X^Y,[]),np(Y^K)]).

% NP ->N
rule(np(X),[n(X)]).



%New Question rules
rule(vp(K,[WH]),[tv(Y,[WH]),np(Y^K)]).
rule(s(X,[WH]),[vp(X,[WH])]).

% WH QUESTIONS rules
rule(Y,[whpr(X^Y),vp(X,[])]).
rule(ynq(Y),[aux, np(X^Y),vp(X,[])]).
rule(Z,[whpr((X^Y)^Z), inv_s(Y,[X])]).
rule(inv_s(Y,[WH]),[aux, np(X^Y),vp(X,[WH])]).

%rule(vp(X^W),[tv(X^Y),n(Y^W)]).

% VP -> DTV NP NP eg: I gave Sue a burger
% VP -> DTV NP PP eg: I gave a burger to Sue
% VP -> VP PP eg: The top shelf contains eggs in a box
% VP -> SV S eg:
% VP -> ADV VP eg:
% VP -> AUX VP eg:
% DT -> NP POS do we need to handle this? POS->s eg: The upper shelf contains Sam's box
% S -> NP VP eg: The white container contains egg
rule(s(Y),[np(X^Y),vp(X,_)]).

% ...


% ===========================================================
%  Modelchecker:
%  1. If input is a declarative, check if true
%  2. If input is a yes-no question, check if true
%  3. If input is a content question, find answer
% ===========================================================

% model(...,...)

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

s(forall(A,imp(and(and(container(A),blue(A)),exists(B,and(and(shelf(B),top(B)),on(A,B)))),
and(exists(C,and(sandwich(C),contains(A,C))),meat(D^has(C^contains(A,C),D))))))