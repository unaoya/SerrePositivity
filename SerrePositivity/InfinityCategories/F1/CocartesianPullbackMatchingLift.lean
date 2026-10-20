module

public import SerrePositivity.InfinityCategories.F1.BaseChange

/-!
概要：底変換上の任意の辺と同じ始点・底を持ち、元の全空間でも cocartesian な lift を選ぶ。
方針：元の fibration で lift し、指定された底の辺との pullback に組み合わせる。
規約：底や全空間の quasicategory 性はこの選択には不要。
使われ方：底変換で cocartesian 辺の像を検出する比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 任意の底変換の辺は、元の全空間で cocartesian な同じ始点・底の lift を持つ。 -/
lemma exists_cocartesianPullbackMatchingLift {E A B : SSet.{u}}
    (p : E ⟶ B) [CocartesianFibration p] (f : A ⟶ B) (e : (pullback p f) _⦋1⦌) :
    ∃ h : (pullback p f) _⦋1⦌,
      (pullback p f).δ 1 h = (pullback p f).δ 1 e ∧
      (pullback.snd p f).app (Opposite.op ⦋1⦌) h = (pullback.snd p f).app _ e ∧
      IsCocartesianEdge (pullback.snd p f) h ∧
      IsCocartesianEdge p ((pullback.fst p f).app (Opposite.op ⦋1⦌) h) := by
  let x := (pullback p f).δ 1 e
  let b : (Δ[1] : SSet.{u}) ⟶ A := SSet.yonedaEquiv.symm e ≫ pullback.snd p f
  have hb : stdSimplex.δ 1 ≫ b = SSet.yonedaEquiv.symm x ≫ pullback.snd p f := by
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
  have hbase : stdSimplex.δ 1 ≫ (b ≫ f) =
      SSet.yonedaEquiv.symm ((pullback.fst p f).app (Opposite.op ⦋0⦌) x) ≫ p := by
    rw [← Category.assoc, hb]
    simp only [← SSet.yonedaEquiv_symm_comp, Category.assoc, pullback.condition]
  obtain ⟨g, hg, hgp, hgc⟩ := CocartesianFibration.mem (p := p) |>.2
    ((pullback.fst p f).app (Opposite.op ⦋0⦌) x) (b ≫ f)
      (by simpa only [SSet.yonedaEquiv_symm_comp] using hbase)
  let h : (Δ[1] : SSet.{u}) ⟶ pullback p f := pullback.lift g b hgp
  have hsrc : stdSimplex.δ 1 ≫ h = SSet.yonedaEquiv.symm x := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hg, SSet.yonedaEquiv_symm_comp]
    · rw [Category.assoc, pullback.lift_snd]
      exact hb
  have hfirst : IsCocartesianEdge p
      ((pullback.fst p f).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv h)) := by
    rw [← SSet.yonedaEquiv_comp, pullback.lift_fst]
    exact hgc
  refine ⟨SSet.yonedaEquiv h, ?_, ?_, isCocartesianEdge_pullback p f _ hfirst, hfirst⟩
  · apply SSet.yonedaEquiv.symm.injective
    rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply]
    exact hsrc
  · rw [← SSet.yonedaEquiv_comp, pullback.lift_snd, SSet.yonedaEquiv_comp,
      Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories
