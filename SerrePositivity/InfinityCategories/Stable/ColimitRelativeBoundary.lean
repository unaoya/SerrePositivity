module
public import SerrePositivity.InfinityCategories.Stable.CoconeRestrictionOppositeFibration
public import SerrePositivity.InfinityCategories.Stable.CartesianInitialBoundary

/-! # 余極限錐の相対境界充填

概要：余極限錐であることと余錐の制限射に対する相対始点境界充填は同値。
方針：余錐の族の始対象性を、反転した制限の cocartesian 輸送を用いて相対条件へ移す。
規約：形状は任意、値域は quasicategory。
使われ方：S3 の普遍余錐の族の充満忠実性。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：余極限錐は図式の任意の指定単体上で始点境界を充填する。
方針：固定図式上の始対象性を相対始対象の境界充填定理に適用する。
規約：余錐の制限の輸送は証明済みの instance から得る。
使われ方：普遍余錐を図式の族として扱うための延長。 -/
lemma IsColimitCone.initialBoundaryLifting {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} {c : JoinCocone p} (hc : IsColimitCone c) :
    InitialBoundaryLifting (coconeRestriction K X) (functorVertex c.val) := by
  exact initialBoundaryLifting_of_isInitialVertex_fiber_op (coconeRestriction K X)
    (functorVertex p) (coconeFamilyVertexEquiv p c)
    ((isColimitCone_iff_isInitialVertex_coconeFamily c).1 hc)

/-- 概要：余極限性と余錐の制限射に対する相対始点境界充填は同値。
方針：fiber の始対象性と相対境界充填の二方向を合わせる。
規約：値域の quasicategory 性以外に仮定はない。
使われ方：S3 の図式の族における普遍性の判定。 -/
lemma isColimitCone_iff_initialBoundaryLifting {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCocone p) :
    IsColimitCone c ↔
      InitialBoundaryLifting (coconeRestriction K X) (functorVertex c.val) :=
  ⟨IsColimitCone.initialBoundaryLifting,
    isColimitCone_of_initialBoundaryLifting_coconeRestriction c⟩

end SerrePositivity.InfinityCategories
