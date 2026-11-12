module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EdgeTerminalCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachment
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquareHorizontalHomotopies

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：余錐の実際の射が同じなら余極限性も同じである。
方針：固定条件で基底の射を同定してから余錐の等号を使う。
規約：基底の射の表示の違いを許す。使われ方：退化図式の余極限の輸送。 -/
lemma isColimitCone_of_val_eq {K X : SSet.{u}} {p q : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (h : c.val = d.val)
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  have hp : p = q := c.property.symm.trans ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ ·) h).trans d.property)
  subst q
  have he : c = d := Subtype.ext h
  rw [he]
  exact hd

/-- 概要：一点の恒等余錐を区間の始点に付加すると標準 span になる。
方針：標準ホーンの二辺の pushout を join の区間同型で移す。
規約：第一の辺は恒等余錐側。使われ方：余極限の付加による判定。 -/
lemma columnSpan_attachment_isPushout :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0]) (stdSimplex.δ (1 : Fin 2))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁) horn₂₀.ι₀₂ := by
  apply horn₂₀.isPushout.of_iso' (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0)
    (Iso.refl _) (Iso.refl _)
  · simpa using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl.symm
  · simp
  · simp
  · simp

/-- 概要：横方向に一定な四角形は押し出しである。
方針：恒等余錐の付加を取り除き、残る区間図式の終点余錐を使う。
規約：値域には Quasicategory のみを仮定する。使われ方：恒等射の三角形。 -/
lemma squareColumnDiagram_isPushout {X : SSet.{u}} [Quasicategory X]
    (g : (Δ[1] : SSet.{u}) ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram g) := by
  let R := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram g
  let x := SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ g)
  let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (SSet.yonedaEquiv.symm x) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone x
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ snd (Δ[1] : SSet.{u}) Δ[1] =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge]
  have hj : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R = c.val := by
    change _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ (snd Δ[1] Δ[1] ≫ g)) = SSet.const x
    rw [Category.assoc, ← Category.assoc horn₂₀.ι₀₁, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge,
      ← Category.assoc _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge, hb, SSet.const_comp, SSet.comp_const]
    have hv : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
        stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by decide
    dsimp only [x]
    rw [SSet.yonedaEquiv_comp, hv]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_colimit_attachment c
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_isColimit x) (stdSimplex.δ (1 : Fin 2))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁) horn₂₀.ι₀₂
    columnSpan_attachment_isPushout hj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone R)).2
  apply isColimitCone_of_val_eq _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone g) _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone_isColimit g)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle (0 : Fin 2) ≫ snd (Δ[1] : SSet.{u}) Δ[1] = stdSimplex.σ 1 := by
    apply SSet.yonedaEquiv.injective
    decide
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap horn₂₀.ι₀₂ (𝟙 (Δ[0] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_right]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight, Category.assoc, Iso.hom_inv_id_assoc]
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ (snd Δ[1] Δ[1] ≫ g)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ stdSimplex.σ 1 ≫ g
  rw [← Category.assoc, hr, Category.assoc, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0), hs]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
