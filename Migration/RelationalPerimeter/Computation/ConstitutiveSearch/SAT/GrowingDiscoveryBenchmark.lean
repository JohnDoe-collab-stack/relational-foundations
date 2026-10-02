import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.SecondAuditCausalBenchmark
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitStackedSymmetricFamily
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.GrowingDiscoveryFamily

set_option linter.defProp false

/-!
# Growing endogenous-discovery benchmark

This module strengthens the second-audit discovery regression from one fixed
decoy to an unbounded family.  The only candidate source is the current CNF.
For input `n`, its first clause contains `n + 1` occurrences of a decoy
variable.  The useful flip-symmetric variable occurs only afterwards.

The extraction run therefore produces the decoys before the useful variable,
the recursive explorer rejects every decoy occurrence, and discovery succeeds
after exactly `n + 2` attempts.  Neither the useful variable nor its position
is passed to the discovery engine.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Appending after a repeated prefix only changes its supplied tail. -/
theorem copiesBefore_append
    {α : Type}
    (count : Nat)
    (value : α)
    (left right : List α) :
    copiesBefore count value left ++ right =
      copiesBefore count value (left ++ right) := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change
        value :: (copiesBefore count value left ++ right) =
          value :: copiesBefore count value (left ++ right)
      rw [inductionHypothesis]

/-- Candidate traversal commutes with the explicit prefix constructor. -/
theorem Clause.candidateVariables_copiesBefore
    (count : Nat)
    (literal : Literal)
    (tail : Clause) :
    Clause.candidateVariables (copiesBefore count literal tail) =
      copiesBefore count literal.candidateVariable
        (Clause.candidateVariables tail) := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change
        literal.candidateVariable ::
            Clause.candidateVariables
              (copiesBefore count literal tail) =
          literal.candidateVariable ::
            copiesBefore count literal.candidateVariable
              (Clause.candidateVariables tail)
      rw [inductionHypothesis]

/-- The clause extractor charges exactly one visit per repeated literal. -/
theorem extractClauseCandidateRun_copiesBefore_literalVisits
    (count : Nat)
    (literal : Literal) :
    (extractClauseCandidateRun
      (copiesBefore count literal [])).stats.literalVisits = count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change
        (extractClauseCandidateRun
          (copiesBefore count literal [])).stats.literalVisits + 1 =
            count + 1
      exact congrArg (fun visits => visits + 1) inductionHypothesis

/-- One failed head preserves the tail result and charges one attempt. -/
theorem exploreStructuralCandidates_cons_failure
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (decoy : Var)
    (tail : List Var)
    (decoyFails :
      tryEndogenousFlipCandidate state decoy = none) :
    (exploreStructuralCandidates
      state
      (decoy :: tail)).discovered? =
        (exploreStructuralCandidates state tail).discovered? /\
      (exploreStructuralCandidates
        state
        (decoy :: tail)).attempts =
          (exploreStructuralCandidates state tail).attempts + 1 := by
  change
    (match tryEndogenousFlipCandidate state decoy with
      | some candidateDiscovery =>
          ({ discovered? := some ⟨decoy, candidateDiscovery⟩
             attempts := 1 } : EndogenousDiscoveryOutcome state)
      | none =>
          let tailRun := exploreStructuralCandidates state tail
          ({ discovered? := tailRun.discovered?
             attempts := tailRun.attempts + 1 } :
            EndogenousDiscoveryOutcome state)).discovered? =
        (exploreStructuralCandidates state tail).discovered? /\
      (match tryEndogenousFlipCandidate state decoy with
        | some candidateDiscovery =>
            ({ discovered? := some ⟨decoy, candidateDiscovery⟩
               attempts := 1 } : EndogenousDiscoveryOutcome state)
        | none =>
            let tailRun := exploreStructuralCandidates state tail
            ({ discovered? := tailRun.discovered?
               attempts := tailRun.attempts + 1 } :
              EndogenousDiscoveryOutcome state)).attempts =
        (exploreStructuralCandidates state tail).attempts + 1
  rw [decoyFails]
  exact ⟨rfl, rfl⟩

/-- Repeated failed heads preserve the tail result and charge every head. -/
theorem exploreStructuralCandidates_copiesBefore_failure
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (count : Nat)
    (decoy : Var)
    (tail : List Var)
    (decoyFails :
      tryEndogenousFlipCandidate state decoy = none) :
    let prefixed :=
      exploreStructuralCandidates
        state
        (copiesBefore count decoy tail)
    let tailRun := exploreStructuralCandidates state tail
    prefixed.discovered? = tailRun.discovered? /\
      prefixed.attempts = tailRun.attempts + count := by
  induction count with
  | zero =>
      exact ⟨rfl, rfl⟩
  | succ count inductionHypothesis =>
      have headStep :=
        exploreStructuralCandidates_cons_failure
          state
          decoy
          (copiesBefore count decoy tail)
          decoyFails
      rcases inductionHypothesis with ⟨discoveredExact, attemptsExact⟩
      change
        (exploreStructuralCandidates
            state
            (decoy :: copiesBefore count decoy tail)).discovered? =
            (exploreStructuralCandidates state tail).discovered? /\
          (exploreStructuralCandidates
            state
            (decoy :: copiesBefore count decoy tail)).attempts =
            (exploreStructuralCandidates state tail).attempts +
              (count + 1)
      constructor
      · exact Eq.trans headStep.1 discoveredExact
      · rw [headStep.2, attemptsExact]
        exact Nat.add_assoc _ _ _

/-- A successful head is returned after exactly one attempted candidate. -/
theorem exploreStructuralCandidates_cons_success
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidate : Var)
    (tail : List Var)
    (candidateFound :
      tryEndogenousFlipCandidate state candidate ≠ none) :
    exists discovery,
      (exploreStructuralCandidates
        state
        (candidate :: tail)).discovered? = some discovery /\
      discovery.var = candidate /\
      (exploreStructuralCandidates
        state
        (candidate :: tail)).attempts = 1 := by
  cases found : tryEndogenousFlipCandidate state candidate with
  | none =>
      exact False.elim (candidateFound found)
  | some evidence =>
      refine ⟨⟨candidate, evidence⟩, ?_, rfl, ?_⟩
      · unfold exploreStructuralCandidates
        rw [found]
      · unfold exploreStructuralCandidates
        rw [found]

/-- The anchor and useful split variable are distinct. -/
theorem growingDiscoveryAnchor_ne_split
    (input : Nat) :
    growingDiscoveryAnchorVar input ≠
      growingDiscoverySplitVar input := by
  unfold growingDiscoveryAnchorVar growingDiscoverySplitVar
  exact Nat.ne_of_gt (Nat.lt_succ_self (input + 2))

/-- The decoy variable differs from the useful variable. -/
theorem growingDiscoveryDecoy_ne_split
    (input : Nat) :
    0 ≠ growingDiscoverySplitVar input :=
  fun impossible => Nat.noConfusion impossible

/-- The decoy variable also differs from the anchor. -/
theorem growingDiscoveryDecoy_ne_anchor
    (input : Nat) :
    0 ≠ growingDiscoveryAnchorVar input :=
  fun impossible => Nat.noConfusion impossible

/-- A positive-zero prefix avoids every variable distinct from zero. -/
theorem Clause.copiesBefore_positiveZero_avoids
    (count : Nat)
    (var : Var)
    (different : 0 ≠ var) :
    Clause.AvoidsVar
      var
      (copiesBefore count (Literal.positive 0) []) := by
  induction count with
  | zero =>
      exact True.intro
  | succ count inductionHypothesis =>
      exact ⟨different, inductionHypothesis⟩

/-- A negative zero literal is absent from every positive-zero prefix. -/
theorem Clause.contains_negativeZero_copiesBefore_positiveZero
    (count : Nat) :
    Clause.containsLiteral
        (Literal.negative 0)
        (copiesBefore count (Literal.positive 0) []) =
      false := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change
        (if Literal.positive 0 = Literal.negative 0 then
            true
          else
            Clause.containsLiteral
              (Literal.negative 0)
              (copiesBefore count (Literal.positive 0) [])) =
          false
      rw [if_neg]
      · exact inductionHypothesis
      · intro impossible
        cases impossible

/-- Flipping literal polarity preserves the number of CNF clauses. -/
theorem Cnf.flipAt_length
    (var : Var)
    (formula : Cnf) :
    (Cnf.flipAt var formula).length = formula.length := by
  induction formula with
  | nil =>
      rfl
  | cons clause rest inductionHypothesis =>
      change
        (Cnf.flipAt var rest).length + 1 =
          rest.length + 1
      exact congrArg (fun length => length + 1) inductionHypothesis

/-- The whole decoy clause avoids the useful split variable. -/
theorem growingDiscoveryDecoyClause_avoids_split
    (input : Nat) :
    Clause.AvoidsVar
      (growingDiscoverySplitVar input)
      (growingDiscoveryDecoyClause input) :=
  Clause.copiesBefore_positiveZero_avoids
    (input + 1)
    (growingDiscoverySplitVar input)
    (growingDiscoveryDecoy_ne_split input)

/-- The useful symmetric body contains no occurrence of the decoy variable. -/
theorem growingDiscoveryBody_avoids_decoy
    (input : Nat) :
    Cnf.AvoidsVar
      0
      (symmetricBlockFamily
        (growingDiscoverySplitVar input)
        (growingDiscoveryAnchorVar input)
        []) := by
  refine ⟨?_, ?_, True.intro⟩
  · exact
      ⟨fun same =>
          (growingDiscoveryDecoy_ne_split input) same.symm,
        fun same =>
          (growingDiscoveryDecoy_ne_anchor input) same.symm,
        True.intro⟩
  · exact
      ⟨fun same =>
          (growingDiscoveryDecoy_ne_split input) same.symm,
        fun same =>
          (growingDiscoveryDecoy_ne_anchor input) same.symm,
        True.intro⟩

/-- The decoy prefix preserves the useful flip symmetry. -/
theorem growingDiscovery_flipSymmetric
    (input : Nat) :
    FlipSymmetricAt
      (growingDiscoveryFormula input)
      (growingDiscoverySplitVar input) := by
  unfold growingDiscoveryFormula
  change
    FlipSymmetricAt
      ([growingDiscoveryDecoyClause input] ++
        symmetricBlockFamily
          (growingDiscoverySplitVar input)
          (growingDiscoveryAnchorVar input)
          [])
      (growingDiscoverySplitVar input)
  apply FlipSymmetricAt.prepend_avoiding
  · exact
      ⟨growingDiscoveryDecoyClause_avoids_split input,
        True.intro⟩
  · apply symmetricBlockFamily_flipSymmetric
    · exact growingDiscoveryAnchor_ne_split input
    · exact True.intro

/-- Checked root freshness for the decoy variable. -/
def growingDiscoveryDecoyCheckedFresh
    (input : Nat) :
    StructuralDecisionsAvoid
      0
      (growingDiscoveryRoot input).context.decisions :=
  structuralDecisionsAvoid_of_check_true
    0
    (growingDiscoveryRoot input).context.decisions
    rfl

/-- The false decoy branch retains the whole presented formula. -/
theorem growingDiscoveryDecoyFalse_formula
    (input : Nat)
    (fresh :
      StructuralDecisionsAvoid
        0
        (growingDiscoveryRoot input).context.decisions) :
    (GeneratedStructuralBranchContext.child
      (growingDiscoveryRoot input)
      0
      false
      fresh).context.formula =
        growingDiscoveryFormula input := by
  change
    branchResidual
        (growingDiscoveryFormula input)
        0
        false =
      growingDiscoveryFormula input
  unfold growingDiscoveryFormula
  have decoyMiss :
      Clause.containsLiteral
          (Literal.forValue 0 false)
          (growingDiscoveryDecoyClause input) =
        false := by
    change
      Clause.containsLiteral
          (Literal.negative 0)
          (copiesBefore
            (input + 1)
            (Literal.positive 0)
            []) =
        false
    exact
      Clause.contains_negativeZero_copiesBefore_positiveZero
        (input + 1)
  rw [
    branchResidual_cons_miss
      (growingDiscoveryDecoyClause input)
      (symmetricBlockFamily
        (growingDiscoverySplitVar input)
        (growingDiscoveryAnchorVar input)
        [])
      0
      false
      decoyMiss
  ]
  rw [
    Cnf.branchResidual_eq_self
      (growingDiscoveryBody_avoids_decoy input)
      false
  ]

/-- The true decoy branch drops its head clause and retains the useful body. -/
theorem growingDiscoveryDecoyTrue_formula
    (input : Nat)
    (fresh :
      StructuralDecisionsAvoid
        0
        (growingDiscoveryRoot input).context.decisions) :
    (GeneratedStructuralBranchContext.child
      (growingDiscoveryRoot input)
      0
      true
      fresh).context.formula =
      symmetricBlockFamily
        (growingDiscoverySplitVar input)
        (growingDiscoveryAnchorVar input)
        [] := by
  change
    branchResidual
        (growingDiscoveryFormula input)
        0
        true =
      symmetricBlockFamily
        (growingDiscoverySplitVar input)
        (growingDiscoveryAnchorVar input)
        []
  unfold growingDiscoveryFormula
  have decoyHit :
      Clause.containsLiteral
          (Literal.forValue 0 true)
          (growingDiscoveryDecoyClause input) =
        true := by
    rfl
  rw [
    branchResidual_cons_hit
      (growingDiscoveryDecoyClause input)
      (symmetricBlockFamily
        (growingDiscoverySplitVar input)
        (growingDiscoveryAnchorVar input)
        [])
      0
      true
      decoyHit
  ]
  rw [
    Cnf.branchResidual_eq_self
      (growingDiscoveryBody_avoids_decoy input)
      true
  ]

/-- The useful body has fewer clauses than the flipped presented formula. -/
theorem growingDiscoveryBody_ne_flipFormula
    (input : Nat) :
    symmetricBlockFamily
        (growingDiscoverySplitVar input)
        (growingDiscoveryAnchorVar input)
        [] ≠
      Cnf.flipAt 0 (growingDiscoveryFormula input) := by
  intro normalizedFormulaExact
  have lengthExact := congrArg List.length normalizedFormulaExact
  have leftLength :
      (symmetricBlockFamily
        (growingDiscoverySplitVar input)
        (growingDiscoveryAnchorVar input)
        []).length = 2 :=
    rfl
  have formulaLength :
      (growingDiscoveryFormula input).length = 3 :=
    rfl
  have impossible : 2 = 3 :=
    Eq.trans
      leftLength.symm
      (Eq.trans
        lengthExact
        (Eq.trans
          (Cnf.flipAt_length 0 (growingDiscoveryFormula input))
          formulaLength))
  exact (Nat.ne_of_lt (Nat.lt_succ_self 2)) impossible

/-- The two decoy children cannot satisfy the searched flip relation. -/
theorem growingDiscoveryDecoy_formula_mismatch
    (input : Nat)
    (fresh :
      StructuralDecisionsAvoid
        0
        (growingDiscoveryRoot input).context.decisions) :
    (GeneratedStructuralBranchContext.child
        (growingDiscoveryRoot input)
        0
        true
        fresh).context.formula ≠
      Cnf.flipAt 0
        (GeneratedStructuralBranchContext.child
          (growingDiscoveryRoot input)
          0
          false
          fresh).context.formula :=
  fun formulaExact =>
    growingDiscoveryBody_ne_flipFormula input
      (Eq.trans
        (growingDiscoveryDecoyTrue_formula input fresh).symm
        (Eq.trans
          formulaExact
          (congrArg
            (Cnf.flipAt 0)
            (growingDiscoveryDecoyFalse_formula input fresh))))

/-- Every occurrence of the extracted decoy is rejected by the actual finder. -/
theorem growingDiscoveryDecoyCandidate_none
    (input : Nat) :
    tryEndogenousFlipCandidate
        (growingDiscoveryRoot input)
        0 =
      none :=
  tryEndogenousFlipCandidate_none_of_formula_mismatch
    (growingDiscoveryRoot input)
    0
    rfl
    (growingDiscoveryDecoy_formula_mismatch
      input
      (growingDiscoveryDecoyCheckedFresh input))

/-- Checked root freshness for the useful variable. -/
def growingDiscoveryCheckedFresh
    (input : Nat) :
    StructuralDecisionsAvoid
      (growingDiscoverySplitVar input)
      (growingDiscoveryRoot input).context.decisions :=
  structuralDecisionsAvoid_of_check_true
    (growingDiscoverySplitVar input)
    (growingDiscoveryRoot input).context.decisions
    rfl

/-- Positive relation certifying the eventual useful attempt. -/
def growingDiscoveryExpectedRelation
    (input : Nat) :
    GeneratedStructuralFlipAtRelation
      (growingDiscoverySplitVar input)
      (GeneratedStructuralBranchContext.child
        (growingDiscoveryRoot input)
        (growingDiscoverySplitVar input)
        false
        (growingDiscoveryCheckedFresh input))
      (GeneratedStructuralBranchContext.child
        (growingDiscoveryRoot input)
        (growingDiscoverySplitVar input)
        true
        (growingDiscoveryCheckedFresh input)) :=
  flipSymmetricSiblingRelation
    (growingDiscoveryRoot input)
    (growingDiscoverySplitVar input)
    (growingDiscoveryCheckedFresh input)
    (growingDiscovery_flipSymmetric input)

/-- The useful candidate succeeds when exploration eventually reaches it. -/
theorem growingDiscoveryUsefulCandidate_found
    (input : Nat) :
    tryEndogenousFlipCandidate
        (growingDiscoveryRoot input)
        (growingDiscoverySplitVar input) ≠
      none :=
  tryEndogenousFlipCandidate_found_of_relation
    (growingDiscoveryRoot input)
    (growingDiscoverySplitVar input)
    rfl
    (growingDiscoveryExpectedRelation input)

/-- Exact candidate order produced by traversing the presented CNF. -/
theorem growingDiscovery_candidates
    (input : Nat) :
    extractStructuralCandidates
        (growingDiscoveryRoot input) =
      copiesBefore
        (input + 1)
        0
        [growingDiscoverySplitVar input,
          growingDiscoveryAnchorVar input,
          growingDiscoverySplitVar input,
          growingDiscoveryAnchorVar input] := by
  unfold extractStructuralCandidates runCandidateExtraction
  rw [extractCnfCandidateRun_candidates]
  change
    Clause.candidateVariables
          (copiesBefore
            (input + 1)
            (Literal.positive 0)
            []) ++
        [growingDiscoverySplitVar input,
          growingDiscoveryAnchorVar input,
          growingDiscoverySplitVar input,
          growingDiscoveryAnchorVar input] =
      copiesBefore
        (input + 1)
        0
        [growingDiscoverySplitVar input,
          growingDiscoveryAnchorVar input,
          growingDiscoverySplitVar input,
          growingDiscoveryAnchorVar input]
  rw [Clause.candidateVariables_copiesBefore]
  exact
    copiesBefore_append
      (input + 1)
      0
      []
      [growingDiscoverySplitVar input,
        growingDiscoveryAnchorVar input,
        growingDiscoverySplitVar input,
        growingDiscoveryAnchorVar input]

/-- Extraction charges all three clauses and every literal it traverses. -/
theorem growingDiscovery_extraction_stats
    (input : Nat) :
    (runCandidateExtraction
        (growingDiscoveryRoot input)).stats.clauseVisits = 3 /\
      (runCandidateExtraction
        (growingDiscoveryRoot input)).stats.literalVisits =
          input + 5 := by
  constructor
  · rfl
  · change
      (extractClauseCandidateRun
          (copiesBefore
            (input + 1)
            (Literal.positive 0)
            [])).stats.literalVisits +
          4 =
        input + 5
    rw [extractClauseCandidateRun_copiesBefore_literalVisits]

/--
The useful candidate is discovered only after all `input + 1` extracted decoy
occurrences have actually failed.  Thus the useful position and charged number
of attempts grow with the input.
-/
theorem growingDiscovery_found_after_exact_attempts
    (input : Nat) :
    exists discovery,
      (runEndogenousFlipDiscovery
        (growingDiscoveryRoot input)).outcome.discovered? =
          some discovery /\
      discovery.var = growingDiscoverySplitVar input /\
      (runEndogenousFlipDiscovery
        (growingDiscoveryRoot input)).outcome.attempts =
          input + 2 := by
  rcases
      exploreStructuralCandidates_cons_success
        (growingDiscoveryRoot input)
        (growingDiscoverySplitVar input)
        [growingDiscoveryAnchorVar input,
          growingDiscoverySplitVar input,
          growingDiscoveryAnchorVar input]
        (growingDiscoveryUsefulCandidate_found input) with
    ⟨discovery, tailFound, selected, tailAttempts⟩
  have prefixRun :=
    exploreStructuralCandidates_copiesBefore_failure
      (growingDiscoveryRoot input)
      (input + 1)
      0
      [growingDiscoverySplitVar input,
        growingDiscoveryAnchorVar input,
        growingDiscoverySplitVar input,
        growingDiscoveryAnchorVar input]
      (growingDiscoveryDecoyCandidate_none input)
  rcases prefixRun with ⟨prefixFound, prefixAttempts⟩
  have candidatesExact := growingDiscovery_candidates input
  have discoveredCandidatesExact :=
    congrArg
      (fun candidates =>
        (exploreStructuralCandidates
          (growingDiscoveryRoot input)
          candidates).discovered?)
      candidatesExact
  have attemptCandidatesExact :=
    congrArg
      (fun candidates =>
        (exploreStructuralCandidates
          (growingDiscoveryRoot input)
          candidates).attempts)
      candidatesExact
  have tailAttemptsCharged :=
    congrArg
      (fun attempts => attempts + (input + 1))
      tailAttempts
  have attemptsArithmetic :
      1 + (input + 1) = input + 2 :=
    Eq.trans
      (Nat.add_assoc 1 input 1).symm
      (Eq.trans
        (congrArg
          (fun value => value + 1)
          (Nat.add_comm 1 input))
        rfl)
  refine ⟨discovery, ?_, selected, ?_⟩
  · exact
      Eq.trans
        discoveredCandidatesExact
        (Eq.trans prefixFound tailFound)
  · exact
      Eq.trans
        attemptCandidatesExact
        (Eq.trans
          prefixAttempts
          (Eq.trans tailAttemptsCharged attemptsArithmetic))

/-! ## Stronger family with pairwise distinct decoy variables -/

/-- Structural extraction returns exactly the announced distinct variables. -/
theorem distinctDecoyClause_candidates
    (count : Nat) :
    (distinctDecoyClause count).candidateVariables =
      distinctDecoyVariables count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change
        count :: (distinctDecoyClause count).candidateVariables =
          count :: distinctDecoyVariables count
      rw [inductionHypothesis]

/-- The distinct decoy list has exactly the requested length. -/
theorem distinctDecoyVariables_length
    (count : Nat) :
    (distinctDecoyVariables count).length = count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change (distinctDecoyVariables count).length + 1 = count + 1
      exact congrArg (fun length => length + 1) inductionHypothesis

/-- Every variable in the descending decoy list is below its count. -/
theorem distinctDecoyVariables_mem_lt
    (count : Nat)
    (candidate : Var)
    (member : candidate ∈ distinctDecoyVariables count) :
    candidate < count := by
  induction count with
  | zero =>
      cases member
  | succ prior inductionHypothesis =>
      cases member with
      | head =>
          exact Nat.lt_succ_self candidate
      | tail _ tailMember =>
          exact
            Nat.lt_trans
              (inductionHypothesis tailMember)
              (Nat.lt_succ_self prior)

/-- A selected decoy occurs positively in its common carrier clause. -/
theorem distinctDecoyClause_contains_positive
    (count : Nat)
    (candidate : Var)
    (member : candidate ∈ distinctDecoyVariables count) :
    Clause.containsLiteral
        (Literal.positive candidate)
        (distinctDecoyClause count) =
      true := by
  induction count with
  | zero =>
      cases member
  | succ count inductionHypothesis =>
      cases member with
      | head =>
          change
            (if Literal.positive candidate = Literal.positive candidate
              then true
              else Clause.containsLiteral
                (Literal.positive candidate)
                (distinctDecoyClause candidate)) = true
          rw [if_pos rfl]
      | tail _ tailMember =>
          have candidateLt : candidate < count :=
            distinctDecoyVariables_mem_lt
              count
              candidate
              tailMember
          have different : count ≠ candidate := by
            intro same
            subst candidate
            exact (Nat.lt_irrefl count) candidateLt
          have literalDifferent :
              Literal.positive count ≠
                Literal.positive candidate := by
            intro same
            exact different (Literal.positive.inj same)
          change
            (if Literal.positive count = Literal.positive candidate
              then true
              else Clause.containsLiteral
                (Literal.positive candidate)
                (distinctDecoyClause count)) = true
          rw [if_neg literalDifferent]
          exact inductionHypothesis tailMember

/-- No negative literal occurs in the all-positive distinct decoy clause. -/
theorem distinctDecoyClause_contains_negative_false
    (count : Nat)
    (candidate : Var) :
    Clause.containsLiteral
        (Literal.negative candidate)
        (distinctDecoyClause count) =
      false := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      have different :
          Literal.positive count ≠
            Literal.negative candidate := by
        intro impossible
        cases impossible
      change
        (if Literal.positive count = Literal.negative candidate
          then true
          else Clause.containsLiteral
            (Literal.negative candidate)
            (distinctDecoyClause count)) = false
      rw [if_neg different]
      exact inductionHypothesis

/-- The extractor charges one literal visit per distinct decoy. -/
theorem distinctDecoyClause_extraction_literalVisits
    (count : Nat) :
    (extractClauseCandidateRun
      (distinctDecoyClause count)).stats.literalVisits = count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change
        (extractClauseCandidateRun
          (distinctDecoyClause count)).stats.literalVisits + 1 =
            count + 1
      exact congrArg (fun visits => visits + 1) inductionHypothesis

/-- A list of failed candidates preserves the tail outcome and charges its length. -/
theorem exploreStructuralCandidates_append_failure
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    ∀ (candidates tail : List Var),
      (∀ candidate : Var,
        candidate ∈ candidates →
          tryEndogenousFlipCandidate state candidate = none) →
      let prefixed :=
        exploreStructuralCandidates state (candidates ++ tail)
      let tailRun := exploreStructuralCandidates state tail
      prefixed.discovered? = tailRun.discovered? /\
        prefixed.attempts = tailRun.attempts + candidates.length
  | [], tail, _allFail =>
      ⟨rfl, rfl⟩
  | candidate :: rest, tail, allFail => by
      have headFails :
          tryEndogenousFlipCandidate state candidate = none :=
        allFail candidate (List.Mem.head rest)
      have restFails :
          ∀ restCandidate : Var,
            restCandidate ∈ rest →
              tryEndogenousFlipCandidate state restCandidate = none := by
        intro restCandidate restMember
        exact
          allFail
            restCandidate
            (List.Mem.tail candidate restMember)
      have headStep :=
        exploreStructuralCandidates_cons_failure
          state
          candidate
          (rest ++ tail)
          headFails
      have tailStep :=
        exploreStructuralCandidates_append_failure
          state
          rest
          tail
          restFails
      constructor
      · exact Eq.trans headStep.1 tailStep.1
      · calc
          (exploreStructuralCandidates
              state ((candidate :: rest) ++ tail)).attempts =
              (exploreStructuralCandidates
                state (rest ++ tail)).attempts + 1 :=
            headStep.2
          _ =
              ((exploreStructuralCandidates state tail).attempts +
                rest.length) + 1 :=
            congrArg (fun attempts => attempts + 1) tailStep.2
          _ =
              (exploreStructuralCandidates state tail).attempts +
                (rest.length + 1) :=
            Nat.add_assoc
              (exploreStructuralCandidates state tail).attempts
              rest.length
              1
          _ =
              (exploreStructuralCandidates state tail).attempts +
                (candidate :: rest).length := rfl

/-- Every decoy below `count` avoids any supplied upper bound. -/
theorem distinctDecoyClause_avoids_above
    (count upper : Nat)
    (bounded : count ≤ upper) :
    Clause.AvoidsVar upper (distinctDecoyClause count) := by
  induction count generalizing upper with
  | zero =>
      exact True.intro
  | succ count inductionHypothesis =>
      have headLt : count < upper :=
        Nat.lt_of_succ_le bounded
      have tailBounded : count ≤ upper :=
        Nat.le_trans (Nat.le_succ count) bounded
      exact
        ⟨Nat.ne_of_lt headLt,
          inductionHypothesis upper tailBounded⟩

/-- All distinct decoys avoid the useful split variable above their range. -/
theorem distinctDecoyClause_avoids_split
    (input : Nat) :
    Clause.AvoidsVar
      (growingDiscoverySplitVar input)
      (distinctDecoyClause (input + 1)) :=
  distinctDecoyClause_avoids_above
    (input + 1)
    (growingDiscoverySplitVar input)
    (Nat.le_succ (input + 1))

/-- The useful two-clause body contains none of the distinct decoy variables. -/
theorem distinctGrowingDiscoveryBody_avoids_candidate
    (input candidate : Nat)
    (member :
      candidate ∈ distinctDecoyVariables (input + 1)) :
    Cnf.AvoidsVar
      candidate
      (symmetricBlockFamily
        (growingDiscoverySplitVar input)
        (growingDiscoveryAnchorVar input)
        []) := by
  have candidateBelowCount : candidate < input + 1 :=
    distinctDecoyVariables_mem_lt
      (input + 1)
      candidate
      member
  have candidateBelowSplit :
      candidate < growingDiscoverySplitVar input := by
    unfold growingDiscoverySplitVar
    exact
      Nat.lt_trans
        candidateBelowCount
        (Nat.lt_succ_self (input + 1))
  have candidateBelowAnchor :
      candidate < growingDiscoveryAnchorVar input := by
    unfold growingDiscoveryAnchorVar
    exact
      Nat.lt_trans
        candidateBelowSplit
        (Nat.lt_succ_self (input + 2))
  have splitDifferent :
      growingDiscoverySplitVar input ≠ candidate :=
    Nat.ne_of_gt candidateBelowSplit
  have anchorDifferent :
      growingDiscoveryAnchorVar input ≠ candidate :=
    Nat.ne_of_gt candidateBelowAnchor
  exact
    ⟨⟨splitDifferent, anchorDifferent, True.intro⟩,
      ⟨splitDifferent, anchorDifferent, True.intro⟩,
      True.intro⟩

/-- The distinct decoy prefix preserves the useful flip symmetry. -/
theorem distinctGrowingDiscovery_flipSymmetric
    (input : Nat) :
    FlipSymmetricAt
      (distinctGrowingDiscoveryFormula input)
      (growingDiscoverySplitVar input) := by
  unfold distinctGrowingDiscoveryFormula
  change
    FlipSymmetricAt
      ([distinctDecoyClause (input + 1)] ++
        symmetricBlockFamily
          (growingDiscoverySplitVar input)
          (growingDiscoveryAnchorVar input)
          [])
      (growingDiscoverySplitVar input)
  apply FlipSymmetricAt.prepend_avoiding
  · exact
      ⟨distinctDecoyClause_avoids_split input,
        True.intro⟩
  · apply symmetricBlockFamily_flipSymmetric
    · exact growingDiscoveryAnchor_ne_split input
    · exact True.intro

/-- Root freshness is executable for every candidate in the distinct family. -/
theorem distinctGrowingDiscoveryCheckedFresh
    (input candidate : Nat) :
    StructuralDecisionsAvoid
      candidate
      (distinctGrowingDiscoveryRoot input).context.decisions :=
  structuralDecisionsAvoid_of_check_true
    candidate
    (distinctGrowingDiscoveryRoot input).context.decisions
    rfl

/-- A distinct decoy false branch retains the complete formula. -/
theorem distinctGrowingDiscoveryDecoyFalse_formula
    (input candidate : Nat)
    (member :
      candidate ∈ distinctDecoyVariables (input + 1))
    (fresh :
      StructuralDecisionsAvoid
        candidate
        (distinctGrowingDiscoveryRoot input).context.decisions) :
    (GeneratedStructuralBranchContext.child
      (distinctGrowingDiscoveryRoot input)
      candidate
      false
      fresh).context.formula =
        distinctGrowingDiscoveryFormula input := by
  change
    branchResidual
        (distinctGrowingDiscoveryFormula input)
        candidate
        false =
      distinctGrowingDiscoveryFormula input
  unfold distinctGrowingDiscoveryFormula
  have decoyMiss :
      Clause.containsLiteral
          (Literal.forValue candidate false)
          (distinctDecoyClause (input + 1)) =
        false := by
    change
      Clause.containsLiteral
          (Literal.negative candidate)
          (distinctDecoyClause (input + 1)) =
        false
    exact
      distinctDecoyClause_contains_negative_false
        (input + 1)
        candidate
  rw [
    branchResidual_cons_miss
      (distinctDecoyClause (input + 1))
      (symmetricBlockFamily
        (growingDiscoverySplitVar input)
        (growingDiscoveryAnchorVar input)
        [])
      candidate
      false
      decoyMiss
  ]
  rw [
    Cnf.branchResidual_eq_self
      (distinctGrowingDiscoveryBody_avoids_candidate
        input candidate member)
      false
  ]

/-- A distinct decoy true branch drops its common carrier clause. -/
theorem distinctGrowingDiscoveryDecoyTrue_formula
    (input candidate : Nat)
    (member :
      candidate ∈ distinctDecoyVariables (input + 1))
    (fresh :
      StructuralDecisionsAvoid
        candidate
        (distinctGrowingDiscoveryRoot input).context.decisions) :
    (GeneratedStructuralBranchContext.child
      (distinctGrowingDiscoveryRoot input)
      candidate
      true
      fresh).context.formula =
      symmetricBlockFamily
        (growingDiscoverySplitVar input)
        (growingDiscoveryAnchorVar input)
        [] := by
  change
    branchResidual
        (distinctGrowingDiscoveryFormula input)
        candidate
        true =
      symmetricBlockFamily
        (growingDiscoverySplitVar input)
        (growingDiscoveryAnchorVar input)
        []
  unfold distinctGrowingDiscoveryFormula
  have decoyHit :
      Clause.containsLiteral
          (Literal.forValue candidate true)
          (distinctDecoyClause (input + 1)) =
        true := by
    change
      Clause.containsLiteral
          (Literal.positive candidate)
          (distinctDecoyClause (input + 1)) =
        true
    exact
      distinctDecoyClause_contains_positive
        (input + 1)
        candidate
        member
  rw [
    branchResidual_cons_hit
      (distinctDecoyClause (input + 1))
      (symmetricBlockFamily
        (growingDiscoverySplitVar input)
        (growingDiscoveryAnchorVar input)
        [])
      candidate
      true
      decoyHit
  ]
  rw [
    Cnf.branchResidual_eq_self
      (distinctGrowingDiscoveryBody_avoids_candidate
        input candidate member)
      true
  ]

/-- The useful body cannot equal a flip of the three-clause presented formula. -/
theorem distinctGrowingDiscoveryBody_ne_flipFormula
    (input candidate : Nat) :
    symmetricBlockFamily
        (growingDiscoverySplitVar input)
        (growingDiscoveryAnchorVar input)
        [] ≠
      Cnf.flipAt candidate
        (distinctGrowingDiscoveryFormula input) := by
  intro normalizedFormulaExact
  have lengthExact := congrArg List.length normalizedFormulaExact
  have leftLength :
      (symmetricBlockFamily
        (growingDiscoverySplitVar input)
        (growingDiscoveryAnchorVar input)
        []).length = 2 :=
    rfl
  have formulaLength :
      (distinctGrowingDiscoveryFormula input).length = 3 :=
    rfl
  have impossible : 2 = 3 :=
    Eq.trans
      leftLength.symm
      (Eq.trans
        lengthExact
        (Eq.trans
          (Cnf.flipAt_length
            candidate
            (distinctGrowingDiscoveryFormula input))
          formulaLength))
  exact (Nat.ne_of_lt (Nat.lt_succ_self 2)) impossible

/-- Every extracted distinct decoy fails the searched flip relation. -/
theorem distinctGrowingDiscoveryDecoy_formula_mismatch
    (input candidate : Nat)
    (member :
      candidate ∈ distinctDecoyVariables (input + 1))
    (fresh :
      StructuralDecisionsAvoid
        candidate
        (distinctGrowingDiscoveryRoot input).context.decisions) :
    (GeneratedStructuralBranchContext.child
        (distinctGrowingDiscoveryRoot input)
        candidate
        true
        fresh).context.formula ≠
      Cnf.flipAt candidate
        (GeneratedStructuralBranchContext.child
          (distinctGrowingDiscoveryRoot input)
          candidate
          false
          fresh).context.formula :=
  fun formulaExact =>
    distinctGrowingDiscoveryBody_ne_flipFormula input candidate
      (Eq.trans
        (distinctGrowingDiscoveryDecoyTrue_formula
          input candidate member fresh).symm
        (Eq.trans
          formulaExact
          (congrArg
            (Cnf.flipAt candidate)
            (distinctGrowingDiscoveryDecoyFalse_formula
              input candidate member fresh))))

/-- Every distinct decoy is rejected by the actual executable finder. -/
theorem distinctGrowingDiscoveryDecoyCandidate_none
    (input candidate : Nat)
    (member :
      candidate ∈ distinctDecoyVariables (input + 1)) :
    tryEndogenousFlipCandidate
        (distinctGrowingDiscoveryRoot input)
        candidate =
      none :=
  tryEndogenousFlipCandidate_none_of_formula_mismatch
    (distinctGrowingDiscoveryRoot input)
    candidate
    rfl
    (distinctGrowingDiscoveryDecoy_formula_mismatch
      input
      candidate
      member
      (distinctGrowingDiscoveryCheckedFresh input candidate))

/-- The decoy variables are genuinely pairwise distinct, not repeated padding. -/
theorem distinctDecoyVariables_nodup
    (count : Nat) :
    (distinctDecoyVariables count).Nodup := by
  unfold List.Nodup
  induction count with
  | zero =>
      exact List.Pairwise.nil
  | succ count inductionHypothesis =>
      apply List.Pairwise.cons
      · intro candidate member
        have below : candidate < count :=
          distinctDecoyVariables_mem_lt
            count
            candidate
            member
        exact Nat.ne_of_gt below
      · exact inductionHypothesis

/-- Positive relation certifying the useful attempt after all distinct decoys. -/
def distinctGrowingDiscoveryExpectedRelation
    (input : Nat) :
    GeneratedStructuralFlipAtRelation
      (growingDiscoverySplitVar input)
      (GeneratedStructuralBranchContext.child
        (distinctGrowingDiscoveryRoot input)
        (growingDiscoverySplitVar input)
        false
        (distinctGrowingDiscoveryCheckedFresh
          input (growingDiscoverySplitVar input)))
      (GeneratedStructuralBranchContext.child
        (distinctGrowingDiscoveryRoot input)
        (growingDiscoverySplitVar input)
        true
        (distinctGrowingDiscoveryCheckedFresh
          input (growingDiscoverySplitVar input))) :=
  flipSymmetricSiblingRelation
    (distinctGrowingDiscoveryRoot input)
    (growingDiscoverySplitVar input)
    (distinctGrowingDiscoveryCheckedFresh
      input (growingDiscoverySplitVar input))
    (distinctGrowingDiscovery_flipSymmetric input)

/-- The useful candidate succeeds after the distinct prefix has been exhausted. -/
theorem distinctGrowingDiscoveryUsefulCandidate_found
    (input : Nat) :
    tryEndogenousFlipCandidate
        (distinctGrowingDiscoveryRoot input)
        (growingDiscoverySplitVar input) ≠
      none :=
  tryEndogenousFlipCandidate_found_of_relation
    (distinctGrowingDiscoveryRoot input)
    (growingDiscoverySplitVar input)
    rfl
    (distinctGrowingDiscoveryExpectedRelation input)

/-- Exact extraction order: all distinct decoys precede the useful block. -/
theorem distinctGrowingDiscovery_candidates
    (input : Nat) :
    extractStructuralCandidates
        (distinctGrowingDiscoveryRoot input) =
      distinctDecoyVariables (input + 1) ++
        [growingDiscoverySplitVar input,
          growingDiscoveryAnchorVar input,
          growingDiscoverySplitVar input,
          growingDiscoveryAnchorVar input] := by
  unfold extractStructuralCandidates runCandidateExtraction
  rw [extractCnfCandidateRun_candidates]
  change
    Clause.candidateVariables (distinctDecoyClause (input + 1)) ++
        [growingDiscoverySplitVar input,
          growingDiscoveryAnchorVar input,
          growingDiscoverySplitVar input,
          growingDiscoveryAnchorVar input] =
      distinctDecoyVariables (input + 1) ++
        [growingDiscoverySplitVar input,
          growingDiscoveryAnchorVar input,
          growingDiscoverySplitVar input,
          growingDiscoveryAnchorVar input]
  rw [distinctDecoyClause_candidates]

/-- Extraction charges three clauses and every distinct decoy literal. -/
theorem distinctGrowingDiscovery_extraction_stats
    (input : Nat) :
    (runCandidateExtraction
        (distinctGrowingDiscoveryRoot input)).stats.clauseVisits = 3 /\
      (runCandidateExtraction
        (distinctGrowingDiscoveryRoot input)).stats.literalVisits =
          input + 5 := by
  constructor
  · rfl
  · change
      (extractClauseCandidateRun
          (distinctDecoyClause (input + 1))).stats.literalVisits +
          4 =
        input + 5
    rw [distinctDecoyClause_extraction_literalVisits]

/--
The executable discovery rejects `input + 1` pairwise distinct variables before
finding the useful split on attempt `input + 2`.
-/
theorem distinctGrowingDiscovery_found_after_exact_attempts
    (input : Nat) :
    exists discovery,
      (runEndogenousFlipDiscovery
        (distinctGrowingDiscoveryRoot input)).outcome.discovered? =
          some discovery /\
      discovery.var = growingDiscoverySplitVar input /\
      (runEndogenousFlipDiscovery
        (distinctGrowingDiscoveryRoot input)).outcome.attempts =
          input + 2 := by
  let usefulTail : List Var :=
    [growingDiscoverySplitVar input,
      growingDiscoveryAnchorVar input,
      growingDiscoverySplitVar input,
      growingDiscoveryAnchorVar input]
  rcases
      exploreStructuralCandidates_cons_success
        (distinctGrowingDiscoveryRoot input)
        (growingDiscoverySplitVar input)
        [growingDiscoveryAnchorVar input,
          growingDiscoverySplitVar input,
          growingDiscoveryAnchorVar input]
        (distinctGrowingDiscoveryUsefulCandidate_found input) with
    ⟨discovery, tailFound, selected, tailAttempts⟩
  have allDecoysFail :
      ∀ candidate : Var,
        candidate ∈ distinctDecoyVariables (input + 1) →
          tryEndogenousFlipCandidate
              (distinctGrowingDiscoveryRoot input)
              candidate =
            none := by
    intro candidate member
    exact
      distinctGrowingDiscoveryDecoyCandidate_none
        input candidate member
  have prefixRun :=
    exploreStructuralCandidates_append_failure
      (distinctGrowingDiscoveryRoot input)
      (distinctDecoyVariables (input + 1))
      usefulTail
      allDecoysFail
  rcases prefixRun with ⟨prefixFound, prefixAttempts⟩
  have candidatesExact := distinctGrowingDiscovery_candidates input
  have discoveredCandidatesExact :=
    congrArg
      (fun candidates =>
        (exploreStructuralCandidates
          (distinctGrowingDiscoveryRoot input)
          candidates).discovered?)
      candidatesExact
  have attemptCandidatesExact :=
    congrArg
      (fun candidates =>
        (exploreStructuralCandidates
          (distinctGrowingDiscoveryRoot input)
          candidates).attempts)
      candidatesExact
  have prefixAttemptsExact :
      (exploreStructuralCandidates
          (distinctGrowingDiscoveryRoot input)
          (distinctDecoyVariables (input + 1) ++ usefulTail)).attempts =
        (exploreStructuralCandidates
          (distinctGrowingDiscoveryRoot input)
          usefulTail).attempts + (input + 1) :=
    Eq.trans
      prefixAttempts
      (congrArg
        (fun count =>
          (exploreStructuralCandidates
            (distinctGrowingDiscoveryRoot input)
            usefulTail).attempts + count)
        (distinctDecoyVariables_length (input + 1)))
  have tailAttemptsCharged :=
    congrArg
      (fun attempts => attempts + (input + 1))
      tailAttempts
  have attemptsArithmetic :
      1 + (input + 1) = input + 2 :=
    Eq.trans
      (Nat.add_assoc 1 input 1).symm
      (Eq.trans
        (congrArg
          (fun value => value + 1)
          (Nat.add_comm 1 input))
        rfl)
  refine ⟨discovery, ?_, selected, ?_⟩
  · exact
      Eq.trans
        discoveredCandidatesExact
        (Eq.trans prefixFound tailFound)
  · exact
      Eq.trans
        attemptCandidatesExact
        (Eq.trans
          prefixAttemptsExact
          (Eq.trans tailAttemptsCharged attemptsArithmetic))

/-- The exact number of executable attempts grows strictly with the input. -/
theorem distinctGrowingDiscovery_attempts_strict
    (input : Nat) :
    (runEndogenousFlipDiscovery
        (distinctGrowingDiscoveryRoot input)).outcome.attempts <
      (runEndogenousFlipDiscovery
        (distinctGrowingDiscoveryRoot (input + 1))).outcome.attempts := by
  rcases distinctGrowingDiscovery_found_after_exact_attempts input with
    ⟨_discovery, _found, _selected, currentAttempts⟩
  rcases distinctGrowingDiscovery_found_after_exact_attempts (input + 1) with
    ⟨_nextDiscovery, _nextFound, _nextSelected, nextAttempts⟩
  rw [currentAttempts, nextAttempts]
  exact Nat.lt_succ_self (input + 2)

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.Clause.candidateVariables_copiesBefore
#print axioms ConstitutiveSearch.SAT.extractClauseCandidateRun_copiesBefore_literalVisits
#print axioms ConstitutiveSearch.SAT.exploreStructuralCandidates_cons_failure
#print axioms ConstitutiveSearch.SAT.exploreStructuralCandidates_copiesBefore_failure
#print axioms ConstitutiveSearch.SAT.exploreStructuralCandidates_cons_success
#print axioms ConstitutiveSearch.SAT.growingDiscoveryAnchor_ne_split
#print axioms ConstitutiveSearch.SAT.growingDiscoveryDecoy_ne_split
#print axioms ConstitutiveSearch.SAT.Clause.copiesBefore_positiveZero_avoids
#print axioms ConstitutiveSearch.SAT.Cnf.flipAt_length
#print axioms ConstitutiveSearch.SAT.growingDiscoveryDecoyClause_avoids_split
#print axioms ConstitutiveSearch.SAT.growingDiscoveryBody_avoids_decoy
#print axioms ConstitutiveSearch.SAT.growingDiscovery_flipSymmetric
#print axioms ConstitutiveSearch.SAT.growingDiscoveryDecoyFalse_formula
#print axioms ConstitutiveSearch.SAT.growingDiscoveryDecoyTrue_formula
#print axioms ConstitutiveSearch.SAT.growingDiscoveryBody_ne_flipFormula
#print axioms ConstitutiveSearch.SAT.growingDiscoveryDecoy_formula_mismatch
#print axioms ConstitutiveSearch.SAT.growingDiscoveryDecoyCandidate_none
#print axioms ConstitutiveSearch.SAT.growingDiscoveryExpectedRelation
#print axioms ConstitutiveSearch.SAT.growingDiscoveryUsefulCandidate_found
#print axioms ConstitutiveSearch.SAT.growingDiscovery_candidates
#print axioms ConstitutiveSearch.SAT.growingDiscovery_extraction_stats
#print axioms ConstitutiveSearch.SAT.growingDiscovery_found_after_exact_attempts
#print axioms ConstitutiveSearch.SAT.distinctDecoyVariables_mem_lt
#print axioms ConstitutiveSearch.SAT.distinctDecoyClause_contains_positive
#print axioms ConstitutiveSearch.SAT.distinctDecoyClause_contains_negative_false
#print axioms ConstitutiveSearch.SAT.exploreStructuralCandidates_append_failure
#print axioms ConstitutiveSearch.SAT.distinctDecoyClause_avoids_split
#print axioms ConstitutiveSearch.SAT.distinctGrowingDiscoveryBody_avoids_candidate
#print axioms ConstitutiveSearch.SAT.distinctGrowingDiscovery_flipSymmetric
#print axioms ConstitutiveSearch.SAT.distinctGrowingDiscoveryDecoy_formula_mismatch
#print axioms ConstitutiveSearch.SAT.distinctGrowingDiscoveryDecoyCandidate_none
#print axioms ConstitutiveSearch.SAT.distinctDecoyVariables_nodup
#print axioms ConstitutiveSearch.SAT.distinctGrowingDiscoveryExpectedRelation
#print axioms ConstitutiveSearch.SAT.distinctGrowingDiscoveryUsefulCandidate_found
#print axioms ConstitutiveSearch.SAT.distinctGrowingDiscovery_candidates
#print axioms ConstitutiveSearch.SAT.distinctGrowingDiscovery_extraction_stats
#print axioms ConstitutiveSearch.SAT.distinctGrowingDiscovery_found_after_exact_attempts
#print axioms ConstitutiveSearch.SAT.distinctGrowingDiscovery_attempts_strict
/- AXIOM_AUDIT_END -/
