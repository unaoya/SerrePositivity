module
public import SerrePositivity.InfinityCategories.Stable.SpanPointJoin
public import SerrePositivity.InfinityCategories.Stable.InitialJoinRestriction
public import SerrePositivity.InfinityCategories.Stable.BinaryCoproductSquare
public import SerrePositivity.InfinityCategories.Stable.ColimitReindex

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
namespace SerrePositivity.InfinityCategories

/-- 概要：二頂点を値とする離散二点図式。
方針：標準零単体二つの直和から頂点の Yoneda 射へ送る。
規約：第一点が x、第二点が y。使われ方：二項余積の余極限の定義。 -/
def binaryPointDiagram {X : SSet.{u}} (x y : X _⦋0⦌) : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X :=
  coprod.desc (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)

/-- 概要：安定 ∞ 圏の二つの指定頂点からなる離散二点図式は余極限を持つ。
方針：零始点の押し出しから余錐を取り、その始対象を除く制限を行う。
規約：通常のホモトピー圏の二項余積の instance は別途構成する。
使われ方：h C の二項余積と前加法構造の基礎。 -/
lemma hasColimit_binaryPointDiagram {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (x y : X _⦋0⦌) : HasColimit (binaryPointDiagram x y) := by
  obtain ⟨R, hz, hRx, hRy, hR⟩ := exists_zeroSourcePushoutSquare x y
  let J := spanPointJoinIso.hom ≫ pushoutSpan R
  let d : JoinCocone J := (pushoutCocone R).restrict spanPointJoinIso.hom
  have hd : IsColimitCone d :=
    (isColimitCone_iff_restrict_of_isIso (pushoutCocone R) spanPointJoinIso.hom).1 hR
  have hsource : joinInl (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ J =
      stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge ≫ R := by
    change _ ≫ (spanPointJoinIso.hom ≫ pushoutSpan R) = _
    rw [← Category.assoc, spanPointJoinIso_source, Category.assoc]
    rw [pushoutSpan, ← Category.assoc horn₂₀.ι₀₁, spanSquareBoundary_bottomEdge]
  have hj : IsInitialVertex (SSet.yonedaEquiv
      (joinInl (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ J)) := by
    rw [hsource, stdSimplex.yonedaEquiv_δ_comp, squareBottomEdge_source]
    exact hz.1
  let e := d.restrict (joinInr (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]))
  have he : IsColimitCone e := (isColimitCone_iff_restrict_joinInr_of_initial J hj d).1 hd
  have hp : joinInr (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ J = binaryPointDiagram x y := by
    have hx' : (coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) ≫
        joinInr (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ J =
          stdSimplex.δ (0 : Fin 2) ≫ squareBottomEdge ≫ R := by
      calc
        _ = (stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₁) ≫ pushoutSpan R := by
          simpa only [Category.assoc] using
            congrArg (fun f => f ≫ pushoutSpan R) spanPointJoinIso_first
        _ = _ := by
          rw [Category.assoc, pushoutSpan, ← Category.assoc horn₂₀.ι₀₁,
            spanSquareBoundary_bottomEdge]
    have hy' : (coprod.inr : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) ≫
        joinInr (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ J =
          stdSimplex.δ (0 : Fin 2) ≫ squareLeftEdge ≫ R := by
      calc
        _ = (stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₂) ≫ pushoutSpan R := by
          simpa only [Category.assoc] using
            congrArg (fun f => f ≫ pushoutSpan R) spanPointJoinIso_second
        _ = _ := by
          rw [Category.assoc, pushoutSpan, ← Category.assoc horn₂₀.ι₀₂,
            spanSquareBoundary_leftEdge]
    apply coprod.hom_ext
    · change _ = coprod.inl ≫ coprod.desc (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)
      rw [coprod.inl_desc]
      apply SSet.yonedaEquiv.injective
      rw [hx', stdSimplex.yonedaEquiv_δ_comp, squareBottomEdge_target, hRx,
        Equiv.apply_symm_apply]
    · change _ = coprod.inr ≫ coprod.desc (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)
      rw [coprod.inr_desc]
      apply SSet.yonedaEquiv.injective
      rw [hy', stdSimplex.yonedaEquiv_δ_comp]
      have hv : X.δ 0 (SSet.yonedaEquiv (squareLeftEdge ≫ R)) = squareVertex R 0 1 := by
        rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, SSet.yonedaEquiv_comp]
        apply congrArg (fun a => R.app (Opposite.op ⦋0⦌) a)
        apply Prod.ext <;> decide
      rw [hv, hRy, Equiv.apply_symm_apply]
  let e' : JoinCocone (binaryPointDiagram x y) := ⟨e.val, e.property.trans hp⟩
  exact ⟨e', (isColimitCone_iff_of_val_eq e' e rfl).2 he⟩

end SerrePositivity.InfinityCategories
