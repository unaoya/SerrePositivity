module
public import SerrePositivity.InfinityCategories.Stable.EdgeTerminalCocone
public import SerrePositivity.InfinityCategories.Core.ColimitAttachment
public import SerrePositivity.InfinityCategories.Stable.SquareHorizontalHomotopies

/-! # 横方向に一定な四角形の押し出し性

概要：一本の辺を二列に並べた四角形は押し出しである。
方針：span は区間に一点の恒等余錐を付加した図式であり、その余極限を区間の終点で判定する。
規約：横の二辺は恒等射。使われ方：恒等射の cofiber を零対象で実現する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：余錐の実際の射が同じなら余極限性も同じである。
方針：固定条件で基底の射を同定してから余錐の等号を使う。
規約：基底の射の表示の違いを許す。使われ方：退化図式の余極限の輸送。 -/
lemma isColimitCone_of_val_eq {K X : SSet.{u}} {p q : K ⟶ X}
    (c : JoinCocone p) (d : JoinCocone q) (h : c.val = d.val)
    (hd : IsColimitCone d) : IsColimitCone c := by
  have hp : p = q := c.property.symm.trans ((congrArg (joinInl K Δ[0] ≫ ·) h).trans d.property)
  subst q
  have he : c = d := Subtype.ext h
  rw [he]
  exact hd

/-- 概要：一点の恒等余錐を区間の始点に付加すると標準 span になる。
方針：標準ホーンの二辺の pushout を join の区間同型で移す。
規約：第一の辺は恒等余錐側。使われ方：余極限の付加による判定。 -/
lemma columnSpan_attachment_isPushout :
    IsPushout (joinInl (Δ[0] : SSet.{u}) Δ[0]) (stdSimplex.δ (1 : Fin 2))
      ((joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁) horn₂₀.ι₀₂ := by
  apply horn₂₀.isPushout.of_iso' (Iso.refl _) (joinStdSimplexIso 0 0)
    (Iso.refl _) (Iso.refl _)
  · simpa using joinStdSimplexIso_zero_inl.symm
  · simp
  · simp
  · simp

/-- 概要：横方向に一定な四角形は押し出しである。
方針：恒等余錐の付加を取り除き、残る区間図式の終点余錐を使う。
規約：値域には Quasicategory のみを仮定する。使われ方：恒等射の三角形。 -/
lemma squareColumnDiagram_isPushout {X : SSet.{u}} [Quasicategory X]
    (g : (Δ[1] : SSet.{u}) ⟶ X) : IsPushoutSquare (squareColumnDiagram g) := by
  let R := squareColumnDiagram g
  let x := SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ g)
  let c : JoinCocone (SSet.yonedaEquiv.symm x) := cosliceIdentityCone x
  have hb : squareBottomEdge ≫ snd (Δ[1] : SSet.{u}) Δ[1] =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    simp [squareBottomEdge]
  have hj : ((joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁) ≫ pushoutSpan R = c.val := by
    change _ ≫ (spanSquareBoundary ≫ (snd Δ[1] Δ[1] ≫ g)) = SSet.const x
    rw [Category.assoc, ← Category.assoc horn₂₀.ι₀₁, spanSquareBoundary_bottomEdge,
      ← Category.assoc squareBottomEdge, hb, SSet.const_comp, SSet.comp_const]
    have hv : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
        stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by decide
    dsimp only [x]
    rw [SSet.yonedaEquiv_comp, hv]
  apply (isColimitCone_iff_restrict_of_colimit_attachment c
    (cosliceIdentityCone_isColimit x) (stdSimplex.δ (1 : Fin 2))
    ((joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁) horn₂₀.ι₀₂
    columnSpan_attachment_isPushout hj (pushoutCocone R)).2
  apply isColimitCone_of_val_eq _ (edgeTerminalCocone g) _ (edgeTerminalCocone_isColimit g)
  have hs : squareTriangle (0 : Fin 2) ≫ snd (Δ[1] : SSet.{u}) Δ[1] = stdSimplex.σ 1 := by
    apply SSet.yonedaEquiv.injective
    decide
  have hr : joinMap horn₂₀.ι₀₂ (𝟙 (Δ[0] : SSet.{u})) ≫ spanCoconeSquareIso.hom =
      (joinStdSimplexIso 1 0).hom ≫ squareTriangle 0 := by
    rw [← spanCoconeSquareIso_right]
    simp only [spanCoconeTriangleRight, Category.assoc, Iso.hom_inv_id_assoc]
  change _ ≫ (spanCoconeSquareIso.hom ≫ (snd Δ[1] Δ[1] ≫ g)) =
    (joinStdSimplexIso 1 0).hom ≫ stdSimplex.σ 1 ≫ g
  rw [← Category.assoc, hr, Category.assoc, ← Category.assoc (squareTriangle 0), hs]

end SerrePositivity.InfinityCategories
