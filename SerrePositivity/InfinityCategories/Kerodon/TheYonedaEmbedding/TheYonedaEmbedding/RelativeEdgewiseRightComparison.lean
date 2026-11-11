module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseRightBoundaryCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.TriangleLongEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseWeightCoordinates

/-!
概要：元の射に対する twisted arrow と指定終点の相対右端比較を固定する。
方針：後合成と右端射影の自然性による引き戻しへの比較を使う。
規約：全空間の Kan 性を要求しない。比較の自明 Kan 性は別に証明する。
使われ方：right unstraightening の全族を Yoneda の全図式へ接続する。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {E B : SSet.{u}} (p : E ⟶ B)

/-- 元の twisted arrow と指定終点を同時に保つ、相対右端比較。 -/
def relativeEdgewiseRightComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision E ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight B) p :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight E) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_naturality p)

lemma relativeEdgewiseRightComparison_fst :
    relativeEdgewiseRightComparison p ≫ pullback.fst _ _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap p :=
  pullback.lift_fst _ _ _

lemma relativeEdgewiseRightComparison_snd :
    relativeEdgewiseRightComparison p ≫ pullback.snd _ _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight E :=
  pullback.lift_snd _ _ _

/-- 重みの同じ底と右半分を保つ充填は、元の引き戻しへの比較を厳密に充填する。 -/
lemma relativeEdgewiseRightComparison_filler {n : ℕ}
    (b : (Δ[n] : SSet.{u}) ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight B) p)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n⦌ ⟶ E)
    (hp : F ≫ p = SSet.yonedaEquiv (b ≫ pullback.fst _ _))
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}).op Δ[n] ≫ F = b ≫ pullback.snd _ _) :
    SSet.yonedaEquiv.symm F ≫ relativeEdgewiseRightComparison p = b := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativeEdgewiseRightComparison_fst]
    apply SSet.yonedaEquiv.injective
    erw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
    exact hp
  · rw [Category.assoc, relativeEdgewiseRightComparison_snd]
    apply SSet.yonedaEquiv.injective
    erw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
    exact congrArg SSet.yonedaEquiv hr

/-- 零次元の重みの右半分の包含は、同じ標準区間の終点包含。 -/
lemma edgewiseWeight_zero_inr_rightAnodyne :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}).op Δ[0]) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}).op Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 0).hom =
      stdSimplex.δ (0 : Fin 2) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_inr]
    congr 1
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    fin_cases i
    rfl
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (f := Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}).op Δ[0]))
      (g := Arrow.mk (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]))
      (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 0) (by
        change 𝟙 (Δ[0] : SSet.{u}) ≫ stdSimplex.δ (0 : Fin 2) = _
        rw [Category.id_comp]
        exact h.symm))).mpr
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.endpointInclusion_rightAnodyne

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
