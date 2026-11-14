module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanPointJoin
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialJoinRestriction
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoproductSquare
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitReindex

/-! # 離散二点図式の余極限

概要：安定 ∞ 圏の任意の二頂点を値とする離散二点図式は余極限を持つ。
方針：零始点の押し出し四角形の余錐を join 表示へ移し、始対象である零始点を忘れる。
規約：二つの入力対象を厳密に指定する。使われ方：h C の二項余積の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：二頂点を値とする離散二点図式。
方針：標準零単体二つの直和から頂点の Yoneda 射へ送る。
規約：第一点が x、第二点が y。使われ方：二項余積の余極限の定義。 -/
def binaryPointDiagram {X : SSet.{u}} (x y : X _⦋0⦌) : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X :=
  coprod.desc (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)

/-- 概要：安定 ∞ 圏の二つの指定頂点からなる離散二点図式は余極限を持つ。
方針：零始点の押し出しから余錐を取り、その始対象を除く制限を行う。
規約：通常のホモトピー圏の二項余積の instance は別途構成する。
使われ方：h C の二項余積と前加法構造の基礎。 -/
lemma hasColimit_binaryPointDiagram {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (x y : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (binaryPointDiagram x y) := by
  obtain ⟨R, hz, hRx, hRy, hR⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_zeroSourcePushoutSquare x y
  let J := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanPointJoinIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone J := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone R).restrict _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanPointJoinIso.hom
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone R) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanPointJoinIso.hom).1 hR
  have hsource : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ J =
      stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R := by
    change _ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanPointJoinIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanPointJoinIso_source, Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc horn₂₀.ι₀₁, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ J)) := by
    rw [hsource, stdSimplex.yonedaEquiv_δ_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source]
    exact hz.1
  let e := d.restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]))
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone e := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isColimitCone_iff_restrict_joinInr_of_initial J hj d).1 hd
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ J = binaryPointDiagram x y := by
    have hx' : (coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ J =
          stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R := by
      calc
        _ = (stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₁) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R := by
          simpa only [Category.assoc] using
            congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanPointJoinIso_first
        _ = _ := by
          rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc horn₂₀.ι₀₁,
            _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
    have hy' : (coprod.inr : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ J =
          stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ R := by
      calc
        _ = (stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₂) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R := by
          simpa only [Category.assoc] using
            congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanPointJoinIso_second
        _ = _ := by
          rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc horn₂₀.ι₀₂,
            _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
    apply coprod.hom_ext
    · change _ = coprod.inl ≫ coprod.desc (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)
      rw [coprod.inl_desc]
      apply SSet.yonedaEquiv.injective
      rw [hx', stdSimplex.yonedaEquiv_δ_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target, hRx,
        Equiv.apply_symm_apply]
    · change _ = coprod.inr ≫ coprod.desc (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)
      rw [coprod.inr_desc]
      apply SSet.yonedaEquiv.injective
      rw [hy', stdSimplex.yonedaEquiv_δ_comp]
      have hv : X.δ 0 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ R)) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 0 1 := by
        rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, SSet.yonedaEquiv_comp]
        apply congrArg (fun a => R.app (Opposite.op ⦋0⦌) a)
        apply Prod.ext <;> decide
      rw [hv, hRy, Equiv.apply_symm_apply]
  let e' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (binaryPointDiagram x y) := ⟨e.val, e.property.trans hp⟩
  exact ⟨e', (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq e' e rfl).2 he⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
