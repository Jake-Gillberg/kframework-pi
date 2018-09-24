require "substitution.k"

module PI-SYNTAX
  imports ID
  imports SUBSTITUTION

  syntax Name ::= Id

  syntax Process ::= NormalProcess
                   | Process "|" Process                   [klabel(Par), left]
                   | "!" Process                           [klabel(Replication)]
                   | "(" "nu" Name ")" Process             [klabel(New)]
	           | "(" Process ")"                       [bracket]

  syntax NormalProcess ::= Name "(" Name ")" "." Process   [binder(2), klabel(Input)]
                         | Name "<" Name ">" "." Process   [klabel(Output)]
                         | "Nil"
			 | NormalProcess "+" NormalProcess [klabel(Or), left]

  syntax priority Replication New Input Output > Or > Par

  syntax KVariable ::= Name

endmodule

module PI
  imports PI-SYNTAX

  configuration <T>
                  <par>
		    <proc multiplicity="*">
		      <k>
		        $PGM:Process
		      </k>
		      <sum>
		        <summand multiplicity="*">.</summand>
		      </sum>
		    </proc>
		  </par>
                </T>

  // STRUCTURAL EQUIVALENCES

  // (P/\equiv, |, 0) is a symmetric monoid
  // P | 0 \equiv P
  // (P | Q) | R \equiv P | (Q | R)
  rule
    <proc>... <k> P:Process | Q:Process => P </k> ...</proc>
    (.Bag => <proc>... <k> Q </k> ...</proc>) [structural]

  rule
    <proc>... <k> Nil </k> ...</proc> => .Bag [structural]

  // (N/\equiv, +, 0) is a symmetric monoid
  rule
    <proc>... <k> N:NormalProcess => . </k>
    <sum> .Bag => <summand> N </summand> </sum> ...</proc> [structural]

  rule
    <summand> N:NormalProcess + M:NormalProcess => N </summand>
    (.Bag => <summand> M </summand>) [structural]

  rule
    <sum>... <summand> Nil </summand> => .Bag ...</sum> [structural]

  rule
    <proc>... <k> . </k> <sum> .Bag </sum> ...</proc> => .Bag [structural]

  //(nu x) 0 \equiv 0
  //(nu x)(nu y)P \equiv (nu y)(nu x)P
  rule
    <k> ( nu X ) P => P </k>
    <bounds>... (.Bag => <bound> X </bound>) ...</bounds> [structural]

  // !(!P) \equiv !P
  // !(Nil | Nil) \equiv !Nil

  rule
    <proc>
      ...
      <k>(. => P[Z / Y])</k>
      (<sum>
        ...
        <summand> X:Name ( Y:Name ) . P:Process </summand>
	...
      </sum> => <sum>.Bag</sum>)
      ...
    </proc>
    <proc>
      ...
      <k>(. => Q)</k>
      (<sum>
        ...
	<summand> X:Name < Z:Name > . Q:Process </summand>
	...
      </sum> => <sum>.Bag</sum>)
      ...
    </proc>

endmodule
