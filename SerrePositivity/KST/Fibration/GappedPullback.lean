module
public import SerrePositivity.KST.Fibration.FullPredicatePullback
public import SerrePositivity.KST.SConstruction.StableModels
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # gapped 条件を両射影で反映する具体的引き戻しの S_n

内部 Hom の引き戻しを元の頂点条件で制限する。反映条件を明示し、実現の極限保存は使わない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 同じ底への単射を後合成して得た引き戻しから、元の底上の引き戻しを回収する。 -/
lemma isPullback_of_postcomp_mono {P X A Y Z : SSet.{u}}
    {p : P ⟶ X} {q : P ⟶ A} {f : X ⟶ Y} {g : A ⟶ Y} (i : Y ⟶ Z) [Mono i]
    (h : IsPullback p q (f ≫ i) (g ≫ i)) : IsPullback p q f g := by
  have hw : p ≫ f = q ≫ g := (cancel_mono i).1 (by simpa only [Category.assoc] using h.w)
  let lift (s : PullbackCone f g) := h.lift s.fst s.snd
    (by simpa only [← Category.assoc] using s.condition =≫ i)
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw lift ?_ ?_ ?_)
  · intro s
    exact h.lift_fst _ _ _
  · intro s
    exact h.lift_snd _ _ _
  · intro s m hm₀ hm₁
    apply h.hom_ext
    · exact hm₀.trans (h.lift_fst _ _ _).symm
    · exact hm₁.trans (h.lift_snd _ _ _).symm

/-- 両射影が gapped 条件を正確に反映する引き戻しは、全 gapped S_n でも引き戻し。 -/
theorem sConstruction_isPullback_of_gapped_reflection {P X A Y : StableModel.{u}}
    {p : P ⟶ X} {q : P ⟶ A} {f : X ⟶ Y} {g : A ⟶ Y}
    (h : IsPullback p.val q.val f.val g.val) (n : ℕ)
    (hr : ∀ F : arNerve n ⟶ P.carrier,
      IsGapped F ↔ IsGapped (F ≫ p.val) ∧ IsGapped (F ≫ q.val)) :
    IsPullback ((sEndofunctor n).map p).val ((sEndofunctor n).map q).val
      ((sEndofunctor n).map f).val ((sEndofunctor n).map g).val := by
  let R := fun v => IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) P.carrier).symm v)
  let RX := fun v => IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) X.carrier).symm v)
  let RA := fun v => IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) A.carrier).symm v)
  have hv : ∀ v, R v ↔ RX (((ihom (arNerve n)).map p.val).app _ v) ∧
      RA (((ihom (arNerve n)).map q.val).app _ v) := by
    intro v
    obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) P.carrier).surjective v
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) ↔
      IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ p.val))) ∧
        IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ q.val)))
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _) F)) ↔
      IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _) (F ≫ p.val))) ∧
        IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _) (F ≫ q.val)))
    simpa only [Equiv.symm_apply_apply] using hr F
  have ht := isPullback_fullPredicates (h.map (ihom (arNerve n))) R RX RA hv
  have he : fullPredicateMap ((ihom (arNerve n)).map p.val) R RX
      (fun v hv' => ((hv v).1 hv').1) = ((sEndofunctor n).map p).val := rfl
  have he' : fullPredicateMap ((ihom (arNerve n)).map q.val) R RA
      (fun v hv' => ((hv v).1 hv').2) = ((sEndofunctor n).map q).val := rfl
  rw [he, he'] at ht
  change IsPullback _ _
    ((gappedSubcomplex n X.carrier).ι ≫ (ihom (arNerve n)).map f.val)
    ((gappedSubcomplex n A.carrier).ι ≫ (ihom (arNerve n)).map g.val) at ht
  rw [← sPostcompCofiber_ι n f.val f.property,
    ← sPostcompCofiber_ι n g.val g.property] at ht
  exact isPullback_of_postcomp_mono (gappedSubcomplex n Y.carrier).ι ht

end SerrePositivity.KST.Fibration
