module RHO-SYNTAX
imports SUBSTITUTION

syntax Proc ::=
              // Empty process
                "Nil"
              // Listen
              | "for(" Name "<-" Name "){" Proc "}" [binder]
              // Persistent listen
              | "for(" Name "<=" Name "){" Proc "}" [binder]
              | "contract" Name "(" Name ")" "=" "{" Proc "}" [binder] // binder? How does this work?
              // Send
              | Name "!(" Proc ")"
              // Evaluate
              | "*" Name
              // New
              | "new" Id "in" "{" Proc "}" [binder]
              // Parallel
              | Proc "|" Proc [left]
              // Misc
              | Exp


syntax Name ::= "@" Proc  // *** We need put the Proc through some algorithm which puts it into its normal form ***
              | Id


// Syntax that will show up b/c of the new construct,
// but that cannot be written (unforgeable things)
syntax HigherProc ::=
                "for(" Chan "<-" Chan "){" HigherProc "}" [binder]
              | "for(" Chan "<=" Chan "){" HigherProc "}" [binder]
              | "contract" Chan "(" Chan ")" "=" "{" HigherProc "}" [binder] // binder? How does this work?
              | Chan "!(" HigherProc ")"
              | "*" Chan
              | "new" Id "in" "{" HigherProc "}" [binder]
              | Proc
              | "#(" Int ")"
              | HigherProc "|" HigherProc [left] // should this be changed to a different category? Procs?
              | "{" HigherProc "}" [bracket]

syntax Chan ::= "@" HigherProc
              | Name

syntax Exp  ::= AExp
              | String

syntax AExp ::= Int | Id
              | AExp "+" AExp [strict,left]
              | AExp "-" AExp [strict,left]
              | AExp "*" AExp [strict,left]
              | AExp "/" AExp [strict,left]
              | AExp AExp [left]
              | "{" AExp "}" [bracket]

syntax KVariable ::= Id

endmodule
module RHO
imports RHO-SYNTAX
// Configuration
configuration <T color="yellow">
                <k multiplicity="*" color="red"> $PGM:Proc </k>
                <NewChannelCounter color="purple"> 0 </NewChannelCounter>
              </T>


// PROCESSES
// Nil process
rule Nil => .

// The semantics for send/receive is being developed. This is the very basic
// version which only receives a channel. There needs to be a pattern-matching
// construct here, which I have and is almost functional. Will update when it is.

// Send/receive, waiting for a channel
rule <k> C:Chan !(P:HigherProc) => . </k>
     <k> for(X:Id <- C:Chan){ S:HigherProc } => S[ @P / X ] </k> [sendreceive]

// Persistent send/receive, waiting for a channel
rule <k> C:Chan !(P:HigherProc) => . </k>
     <k> for(X:Id <= C:Chan){ S:HigherProc } </k>
     (.Bag => <k> S[ @P / X ] </k>) [sendreceive]

// Contracts (persistent send/receive rewritten)
rule <k> contract C:Chan(X:Id) = { P:HigherProc } => for(X <= C){ P } </k>


// Evaluation and Quotation: Inverses
rule <k> ... * @ P:HigherProc  => P ... </k>
rule <k> ... @ * C:Chan  => C ... </k>

// Parallel processes
rule <k> ... P1:HigherProc | P2:HigherProc => P1 ... </k>
     (.Bag => <k> P2 </k>)

// New construct
// It would be better here to have the semantics #(!N:Int), but the
// version of K supported by the K VM available online doesn't support
// this yet; in the final version we'll do it with !N:Int and get rid
// of the NewChannelCounter cell.
rule <k> new X:Id in { P:HigherProc } => P[@ #(I:Int) / X] </k>
     <NewChannelCounter> I => I +Int 1 </NewChannelCounter> [newchannel]

// Delete empty k-cells
rule <k> .K </k> => .

// Delete k-cells which have only an expression in them
rule <k> E:Exp </k> => .

endmodule
