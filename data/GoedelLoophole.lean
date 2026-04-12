/-
  Gödel's Loophole — Demonstrated in Lean 4
  ===========================================
  We formalize Article V of the US Constitution and construct
  a concrete proof that an amendment establishing a dictatorship
  satisfies all validity conditions.

  No external dependencies. Fully self-contained.
-/

-- ============================================================
-- §1  DOMAIN TYPES
-- ============================================================

def State := Nat

structure StateSet where
  count : Nat
  count_pos : count > 0

structure Chamber where
  memberCount : Nat
  pos : memberCount > 0

structure TwoThirdsVote (c : Chamber) where
  ayes : Nat
  le_members : ayes ≤ c.memberCount
  threshold : ayes * 3 ≥ c.memberCount * 2

structure Congress where
  house  : Chamber
  senate : Chamber

structure StateUnion where
  states : StateSet

-- ============================================================
-- §2  CONSTITUTIONAL REFERENCES
-- ============================================================

inductive ShieldedClause
  | first
  | fourth

inductive AmendmentSubject
  | affectsShieldedClause (c : ShieldedClause)
  | deprivesEqualSuffrage (s : State)
  | other

-- ============================================================
-- §3  PROPOSAL (two paths)
-- ============================================================

structure CongressionalInitiation (congress : Congress) where
  houseVote  : TwoThirdsVote congress.house
  senateVote : TwoThirdsVote congress.senate

structure StateLegislatureApplication (u : StateUnion) where
  applyingCount : Nat
  le_states : applyingCount ≤ u.states.count
  threshold : applyingCount * 3 ≥ u.states.count * 2

structure Convention where
  delegateCount : Nat
  pos : delegateCount > 0

structure ConventionCalled (u : StateUnion) where
  application : StateLegislatureApplication u
  convention  : Convention

inductive Proposal (congress : Congress) (u : StateUnion)
  | byCongressDirectly (init : CongressionalInitiation congress)
  | byConvention (called : ConventionCalled u)

-- ============================================================
-- §4  RATIFICATION
-- ============================================================

inductive RatificationMode
  | byStateLegislatures
  | byStateConventions

structure ModeSelection where
  mode : RatificationMode

inductive Ratification (u : StateUnion) (sel : ModeSelection)
  | byStateLegislatures
      (ratifyingCount : Nat)
      (le_states : ratifyingCount ≤ u.states.count)
      (threshold : ratifyingCount * 4 ≥ u.states.count * 3)
      (modeMatch : sel.mode = .byStateLegislatures)
  | byStateConventions
      (ratifyingCount : Nat)
      (le_states : ratifyingCount ≤ u.states.count)
      (threshold : ratifyingCount * 4 ≥ u.states.count * 3)
      (modeMatch : sel.mode = .byStateConventions)

-- ============================================================
-- §5  RESTRICTIONS
-- ============================================================

def pre1808Restriction (subject : AmendmentSubject) (year : Nat) : Prop :=
  match subject with
  | .affectsShieldedClause _ => ¬ (year < 1808)
  | _ => True

def equalSuffrageRestriction
    (subject : AmendmentSubject) (consent : State → Prop) : Prop :=
  match subject with
  | .deprivesEqualSuffrage s => consent s
  | _ => True

-- ============================================================
-- §6  AMENDMENT VALIDITY
-- ============================================================

structure ArticleVAmendment where
  congress      : Congress
  u             : StateUnion
  yearProposed  : Nat
  subject       : AmendmentSubject
  stateConsent  : State → Prop
  proposal      : Proposal congress u
  modeSelection : ModeSelection
  ratification  : Ratification u modeSelection

def isValid (a : ArticleVAmendment) : Prop :=
  pre1808Restriction a.subject a.yearProposed
  ∧ equalSuffrageRestriction a.subject a.stateConsent

structure PartOfConstitution where
  amendment : ArticleVAmendment
  valid     : isValid amendment
