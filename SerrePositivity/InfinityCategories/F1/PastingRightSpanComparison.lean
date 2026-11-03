module
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.ColimitCoconeRestriction
public import SerrePositivity.InfinityCategories.Core.InitialEquivalence
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceRightRestriction
public import SerrePositivity.InfinityCategories.F1.PastingCofinality
public import SerrePositivity.InfinityCategories.Core.PastingCorner
public import SerrePositivity.InfinityCategories.Core.PastingRightSpanIso
public import SerrePositivity.InfinityCategories.Core.PushoutShape

/-! # 標準 span 上での部分長方形の余錐の比較

概要：五頂点図式の余錐は右四角形の標準 span 上への制限で余極限性を判定できる。
方針：右の部分図式の同型を通じ、既に証明した coslice の trivial Kan fibration を移す。
規約：標準 span の二辺は右四角形の下辺・左辺と厳密に一致する。
使われ方：S4 の右四角形と長方形の join 余錐との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右 span の同型を長方形へ含めると右四角形の span の包含になる。
方針：二本の辺で比較し、標準 span の pushout の一意性を使う。
規約：射の厳密な等式。
使われ方：右四角形の押し出し性を部分図式に移す。 -/
lemma pastingRightSpanIso_hom_ι :
    pastingRightSpanIso.{u}.hom ≫ pastingRightSpan.ι ≫ pastingCorner.ι =
      spanSquareBoundary ≫ (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) := by
  change pastingRightSpanFromHorn ≫ pastingRightSpan.ι ≫ pastingCorner.ι = _
  apply horn₂₀.isPushout.hom_ext
  · rw [← Category.assoc, pastingRightSpanFromHorn_left, pastingRightSpanBottom_ι,
      ← Category.assoc, spanSquareBoundary_bottomEdge]
  · rw [← Category.assoc, pastingRightSpanFromHorn_right, pastingRightSpanVertical_ι,
      ← Category.assoc, spanSquareBoundary_leftEdge]

/-- 概要：五頂点図式から標準 span への coslice の制限は trivial Kan fibration。
方針：右の三頂点部分への制限を同型で標準 span に移す。
規約：値域は quasicategory、図式 p は任意。
使われ方：貼り合わせの右側の普遍性の判定。 -/
lemma pastingCornerRestrict_standardSpan_trivialKanFibration {X : SSet.{u}} [Quasicategory X]
    (p : (pastingCorner : SSet.{u}) ⟶ X) :
    TrivialKanFibration
      (sliceUnderRestrict p (pastingRightSpanIso.hom ≫ pastingRightSpan.ι)) := by
  have := pastingCornerRestrict_trivialKanFibration p
  exact sliceUnderRestrict_trivialKanFibration_subcomplexIso p pastingRightSpan pastingRightSpanIso

/-- 概要：五頂点図式の余錐の余極限性は右四角形の標準 span 上で判定できる。
方針：coslice の制限の同値による始対象性の保存と反映を使う。
規約：余錐の頂点は変わらない。
使われ方：S4 の貼り合わせの右側の比較。 -/
lemma pastingCorner_isColimitCone_iff_standardSpan {X : SSet.{u}} [Quasicategory X]
    {p : (pastingCorner : SSet.{u}) ⟶ X} (c : JoinCocone p) :
    IsColimitCone c ↔
      IsColimitCone (c.restrict (pastingRightSpanIso.hom ≫ pastingRightSpan.ι)) := by
  have := pastingCornerRestrict_standardSpan_trivialKanFibration p
  exact (qCatEquivalenceOfTrivialKanFibration
    (sliceUnderRestrict p (pastingRightSpanIso.hom ≫ pastingRightSpan.ι))).isInitialVertex_iff c

end SerrePositivity.InfinityCategories
