%--------------------------------------------------------------------------
% File     : Test.gothm3 : TPTP v8.0.0.
% Domain   : None
% Problem  : question3
% Version  : None
% English  :

% Refs     : https://github.com/epfl-lara/lisa
%          : lisa.utils.tptp.ProofParser
% Source   : [Lisa, Test.gothm3]
% Names    : 

% Status   : Unknown
% Rating   : ?
% Syntax   : ?
% SPC      : FOF_UNK_RFO_SEQ

% Comments : This problem, was printed from a statement in a proof of a theorem by the Lisa theorem prover for submission to proof-producing ATPs.
%--------------------------------------------------------------------------
fof(c1, conjecture, ($true => (~ (ss(cemptySet)) => ~ ((! [Xx]: (ss(Xx))))))).
