/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibTest.GameTheory.BlockingWitness
public import MathEconLibTest.GameTheory.ReductionSupport

/-!
# Simulations as obstruction-witness lifts

A failed weak deviation comparison is an obstruction, including when rewards
are incomparable. Simulation bounds lift these witnesses without requiring
validity of deviation targets. Composing converted lifts retains intermediate
provenance, which implies the bound retained by a converted composite simulation.
The converse need not hold: an endpoint bound can allow more source witnesses
than can pass through the prescribed intermediate deviations.
-/

@[expose] public section

namespace MathEconLibTest.GameTheory.ReductionSupport

open MathEconLib.GameTheory MathEconLibTest.AbstractionExperiments

universe u v w x y z

/-- An admissible deviation violating the weak incumbent comparison. -/
def badDeviation {S : Type u} {I : Type v} {V : Type*} [Preorder V]
    (P : EquilibriumProblem S I V)
    (s : S) (proposal : I × S) : Prop :=
  P.deviation proposal.1 s proposal.2 ∧ ¬ P.value proposal.1 proposal.2 ≤ P.value proposal.1 s

/-- The obstruction view preserves native deviation optimality even for partial orders. -/
theorem isDeviationOptimal_iff_no_badDeviation {S : Type u} {I : Type v} {V : Type*}
    [Preorder V] (P : EquilibriumProblem S I V) (s : S) :
    P.IsDeviationOptimal s ↔ ∀ proposal, ¬ badDeviation P s proposal := by
  constructor
  · intro optimal proposal violation
    exact violation.2 (optimal proposal.1 proposal.2 violation.1)
  · intro absent i t admitted
    exact Classical.byContradiction fun violation => absent (i, t) ⟨admitted, violation⟩

namespace GameSimulation

variable {V W X : Type*} [Preorder V] [Preorder W] [Preorder X]
  {S : Type u} {I : Type v} {T : Type w} {J : Type x} {U : Type y} {K : Type z}
  {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
  {R : EquilibriumProblem U K X}

/-- A simulation's domination bounds lift failures of weak deviation comparisons.
The provenance records the judge map, both admissibility facts, and the bound. -/
def toBadDeviationLift (f : GameSimulation P Q) :
    WitnessLift (badDeviation P) (badDeviation Q) where
  state := f.toFun
  related s q p :=
    p.1 = f.deviatorMap q.1 ∧ Q.deviation q.1 (f.toFun s) q.2 ∧
      P.deviation p.1 s p.2 ∧ Q.value q.1 q.2 ≤ f.valueMap q.1 (P.value p.1 p.2)
  covers s q violation := by
    obtain ⟨p, admitted, bound⟩ := f.deviation_dominated q.1 s q.2 violation.1
    refine ⟨(f.deviatorMap q.1, p), ⟨rfl, violation.1, admitted, bound⟩, admitted, ?_⟩
    intro weak
    exact violation.2 (bound.trans
      (((f.valueMap q.1).monotone weak).trans (f.value_le q.1 s)))

/-- Both conversion orders have the same state translation. -/
theorem toBadDeviationLift_comp_state (g : GameSimulation Q R) (f : GameSimulation P Q) :
    (g.comp f).toBadDeviationLift.state = (g.toBadDeviationLift.comp f.toBadDeviationLift).state :=
  rfl

/-- Intermediate witness provenance implies the composite endpoint bound. -/
theorem toBadDeviationLift_comp_related (g : GameSimulation Q R) (f : GameSimulation P Q)
    {s : S} {r : K × U} {p : I × S}
    (sequential : (g.toBadDeviationLift.comp f.toBadDeviationLift).related s r p) :
    (g.comp f).toBadDeviationLift.related s r p := by
  obtain ⟨q, ⟨judgeG, targetAdmitted, _, boundG⟩,
    ⟨judgeF, _, sourceAdmitted, boundF⟩⟩ := sequential
  refine ⟨judgeF.trans (congrArg f.deviatorMap judgeG), targetAdmitted, sourceAdmitted, ?_⟩
  change R.value r.1 r.2 ≤
    g.valueMap r.1 (f.valueMap (g.deviatorMap r.1) (P.value p.1 p.2))
  apply boundG.trans
  apply (g.valueMap r.1).monotone
  simpa only [judgeG] using boundF

end GameSimulation

namespace WitnessCoherenceBoundary

/-- Validity concerns the incumbent; admitted positive endpoints remain invalid. -/
def menuProblem (admitted : ℕ → Prop) : EquilibriumProblem ℕ Unit ℕ where
  deviation _ s t := s = 0 ∧ admitted t
  value _ s := s
  valid s := s = 0

def source : EquilibriumProblem ℕ Unit ℕ := menuProblem (fun t => t = 1 ∨ t = 2)

def middle : EquilibriumProblem ℕ Unit ℕ := menuProblem (fun t => t = 2)

def target : EquilibriumProblem ℕ Unit ℕ := menuProblem (fun t => t = 1)

/-- The intermediate deviation at two is dominated by the source deviation at two. -/
def first : GameSimulation source middle where
  toFun := id
  deviatorMap := id
  valueMap _ := OrderHom.id
  value_le _ _ := le_rfl
  deviation_dominated _ _s t admitted :=
    ⟨t, ⟨admitted.1, Or.inr admitted.2⟩, le_rfl⟩
  valid_preserves _ valid := valid

/-- The target deviation at one is dominated by the intermediate deviation at two. -/
def second : GameSimulation middle target where
  toFun := id
  deviatorMap := id
  valueMap _ := OrderHom.id
  value_le _ _ := le_rfl
  deviation_dominated _ s t admitted := by
    refine ⟨2, ⟨admitted.1, rfl⟩, ?_⟩
    change t ≤ 2
    rw [admitted.2]
    decide
  valid_preserves _ valid := valid

theorem target_one_bad : badDeviation target 0 ((), 1) :=
  ⟨⟨rfl, rfl⟩, by decide⟩

theorem source_one_bad : badDeviation source 0 ((), 1) :=
  ⟨⟨rfl, Or.inl rfl⟩, by decide⟩

/-- The witness is an admissible obstruction despite its invalid endpoint. -/
theorem source_one_invalid : ¬ source.valid 1 := by
  change ¬ ((1 : ℕ) = 0)
  decide

/-- The final bound alone permits the source deviation at one. -/
theorem direct_accepts_one :
    (second.comp first).toBadDeviationLift.related 0 ((), 1) ((), 1) :=
  ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, Or.inl rfl⟩, le_rfl⟩

/-- Passing through the intermediate deviation requires a source value at least two. -/
theorem sequential_rejects_one :
    ¬ (second.toBadDeviationLift.comp first.toBadDeviationLift).related 0 ((), 1) ((), 1) := by
  rintro ⟨⟨judge, t⟩, secondRelated, firstRelated⟩
  have middleEndpoint : t = 2 := secondRelated.2.2.1.2
  have bound : t ≤ 1 := firstRelated.2.2.2
  rw [middleEndpoint] at bound
  exact (Nat.not_succ_le_self 1) bound

/-- Both lifts still cover the actual target obstruction, using the source deviation at two. -/
theorem sequential_accepts_two :
    (second.toBadDeviationLift.comp first.toBadDeviationLift).related 0 ((), 1) ((), 2) :=
  ⟨((), 2), ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, by decide⟩,
    ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, Or.inr rfl⟩, le_rfl⟩⟩

/-- Conversion preserves composite state maps but does not preserve the provenance relation. -/
theorem conversion_relation_not_equal :
    (second.comp first).toBadDeviationLift.related ≠
      (second.toBadDeviationLift.comp first.toBadDeviationLift).related := by
  intro equal
  exact sequential_rejects_one (equal ▸ direct_accepts_one)

end WitnessCoherenceBoundary
end MathEconLibTest.GameTheory.ReductionSupport
