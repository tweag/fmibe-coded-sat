  $ rocq compile -q -noglob -R ../src FMV -o assumptions.vo assumptions.v
  Axioms:
  Impl.sat is assumed to be guarded.
  progress_falsified_empty :
    forall s s' : Impl.State,
    state_invariant s ->
    falsified_clauses_pending s ->
    Impl.progress s = Impl.Progress s' -> falsified_clauses_pending s'
  backtrack_progress_falsified_pending :
    forall (s : Impl.State) (cause : Impl.Clause) (next : Impl.State),
    backtrack_invariant s ->
    clause_implied_by_store (Impl.state_clauses s) cause ->
    clause_falsified_by_model (Impl.trail_model (Impl.state_trail s)) cause ->
    Impl.backtrack (s, cause) = Some (Impl.Progress next) ->
    falsified_clauses_pending next
  Axioms:
  Impl.sat is assumed to be guarded.
  progress_falsified_empty :
    forall s s' : Impl.State,
    state_invariant s ->
    falsified_clauses_pending s ->
    Impl.progress s = Impl.Progress s' -> falsified_clauses_pending s'
  backtrack_progress_falsified_pending :
    forall (s : Impl.State) (cause : Impl.Clause) (next : Impl.State),
    backtrack_invariant s ->
    clause_implied_by_store (Impl.state_clauses s) cause ->
    clause_falsified_by_model (Impl.trail_model (Impl.state_trail s)) cause ->
    Impl.backtrack (s, cause) = Some (Impl.Progress next) ->
    falsified_clauses_pending next
