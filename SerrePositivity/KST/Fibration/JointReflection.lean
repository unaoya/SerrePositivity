module
public import SerrePositivity.KST.Fibration.FamilyExactness
public import SerrePositivity.KST.SConstruction.CofiberPreservesPushout

/-! # 元の両射影による零対象と実押し出しの共同反映 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 二射影が元の零対象と実押し出しの普遍性を共同で反映するという性質。 -/
structure JointlyReflectsSData {P X A : SSet.{u}} (p : P ⟶ X) (q : P ⟶ A) : Prop where
  zero (v : P _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (p.app (Opposite.op ⦋0⦌) v) →
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (q.app (Opposite.op ⦋0⦌) v) → _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex v
  pushout (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ p) → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ q) → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F

/-- 完全な両射影が共同反映するなら、全 gapped 条件も共同で正確に反映する。 -/
lemma JointlyReflectsSData.isGapped_iff {P X A : StableModel.{u}}
    {p : P ⟶ X} {q : P ⟶ A} (h : JointlyReflectsSData p.val q.val)
    {n : ℕ} (F : arNerve n ⟶ P.carrier) :
    IsGapped F ↔ IsGapped (F ≫ p.val) ∧ IsGapped (F ≫ q.val) := by
  constructor
  · intro hf
    exact ⟨hf.postcomp _ (stableModelHom_preservesSConstructionData p),
      hf.postcomp _ (stableModelHom_preservesSConstructionData q)⟩
  · rintro ⟨hp, hq⟩
    constructor
    · intro i
      exact h.zero _ (hp.1 i) (hq.1 i)
    · intro i j k l hij hjk hkl
      apply h.pushout
      · simpa only [Category.assoc] using hp.2 i j k l hij hjk hkl
      · simpa only [Category.assoc] using hq.2 i j k l hij hjk hkl

/-- 全関手圏での共同反映は、同じ両射影の全頂点評価で確認できる。 -/
lemma JointlyReflectsSData.ihom {P X A : StableModel.{u}} {p : P ⟶ X} {q : P ⟶ A}
    (h : JointlyReflectsSData p.val q.val) (K : SSet.{u}) :
    JointlyReflectsSData ((CategoryTheory.ihom K).map p.val)
      ((CategoryTheory.ihom K).map q.val) where
  zero v hp hq := by
    apply isZeroVertex_of_pointwise
    intro k
    have hp' := isZeroVertex_evaluateFunctorAt hp k
    have hq' := isZeroVertex_evaluateFunctorAt hq k
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((((CategoryTheory.ihom K).map p.val ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app _ v)) at hp'
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((((CategoryTheory.ihom K).map q.val ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app _ v)) at hq'
    rw [ihom_postcomp_evaluate] at hp' hq'
    exact h.zero _ hp' hq'
  pushout F hp hq := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPushoutSquare_of_pointwise
    intro k
    apply h.pushout
    · have hp' := (evaluateFunctorAt_preservesSConstructionData (C := X.carrier) k).2 _ hp
      rwa [Category.assoc, ihom_postcomp_evaluate, ← Category.assoc] at hp'
    · have hq' := (evaluateFunctorAt_preservesSConstructionData (C := A.carrier) k).2 _ hq
      rwa [Category.assoc, ihom_postcomp_evaluate, ← Category.assoc] at hq'

/-- 一方の値域を元の完全同型で置き換えても、共同反映を保つ。 -/
lemma JointlyReflectsSData.postcomp_left_iso {P X A Y : StableModel.{u}}
    {p : P ⟶ X} {q : P ⟶ A} (h : JointlyReflectsSData p.val q.val) (e : X ≅ Y) :
    JointlyReflectsSData (p ≫ e.hom).val q.val := by
  have : IsIso e.hom.val := inferInstanceAs (IsIso (stableModelForget.map e.hom))
  constructor
  · intro v hp hq
    exact h.zero v ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isZeroVertex_iff_map_of_trivialKanFibration e.hom.val _).2 hp) hq
  · intro F hp hq
    exact h.pushout F
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_iff_postcomp_trivialKanFibration e.hom.val _).2 hp) hq

end SerrePositivity.KST.Fibration
