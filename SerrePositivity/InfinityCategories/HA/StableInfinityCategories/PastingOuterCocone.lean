module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingOuterSpanIso

/-! # 四頂点図式の余錐と外側四角形

概要：長方形の余錐を四頂点図式へ制限すると、外側 span 上で外側四角形の余錐になる。
方針：基底の厳密な一致と終端角の一致を使う。
規約：左四角形の押し出し性による五頂点と四頂点の比較は別途必要。
使われ方：S4 の貼り合わせの外側の普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：長方形の余錐を外側 span に制限すると外側四角形の余錐表示に一致する。
方針：基底では外側 span の包含、終端角では正方形の第一三角形を使う。
規約：値域の図式を選ぶ前の形状の等式。使われ方：外側の押し出し判定。 -/
lemma pastingCornerCocone_outerSpan :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.{u}.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner)
      (𝟙 Δ[0]) ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCornerCocone =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stableJoin_prodStdSimplex_hom_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCornerCocone_inl]
    have hι : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase.ι := rfl
    rw [Category.assoc, Category.assoc, hι]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso_hom_ι
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
    have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (horn 2 0 : SSet.{u}) Δ[0] =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[1] Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft := by
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft, Iso.hom_inv_id_assoc]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
    rw [hv]
    simp only [Category.assoc, reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_left]
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide

/-- 概要：長方形の余錐を四頂点図式へ制限する。
方針：五頂点図式への包含に沿う余錐の制限を使う。
規約：左四角形の余極限頂点を含まない基底。使われ方：外側比較の中間余錐。 -/
def pastingOuterCocone {X : SSet.{u}} (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :=
  (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingCocone F).restrict _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner

/-- 概要：四頂点図式上の長方形の余極限性は外側四角形の押し出し性と同値。
方針：外側 span への制限で判定し、形状の等式で外側四角形の余錐と比較する。
規約：値域は quasicategory、左四角形への仮定は不要。
使われ方：S4 の貼り合わせの外側の普遍性の判定。 -/
lemma pastingOuterCocone_isColimitCone_iff_outer {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (pastingOuterCocone F) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) := by
  refine (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase_isColimitCone_iff_standardSpan (pastingOuterCocone F)).trans ?_
  apply _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.restrict, pastingOuterCocone, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingCocone,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare]
  rw [← Category.assoc, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  simp only [Category.id_comp]
  rw [Category.assoc _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner,
    pastingCornerCocone_outerSpan, Category.assoc]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
