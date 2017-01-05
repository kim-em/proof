Set Implicit Arguments.

Structure FancyFunction := {
  source: Type;
  target: Type;
  function: source -> target;
}.

Definition cast (A B: Type) (Q: A=B) (a: A) : B := eq_rect A (fun Z => Z) a B Q.

Structure Example := {
  fancyFunction: FancyFunction;
  sourceEvidence: Prop = fancyFunction.(source);
  targetEvidence: Prop = fancyFunction.(target);
  takes1to1: fancyFunction.(function)(cast(sourceEvidence)(True)) = cast(targetEvidence)(True);
}.