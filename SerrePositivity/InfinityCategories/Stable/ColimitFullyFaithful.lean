module
public import SerrePositivity.InfinityCategories.Stable.MappingSpacePositiveBoundary
public import SerrePositivity.InfinityCategories.Stable.ColimitCoconeFamilies

/-! # 普遍余錐の射影の充満忠実性

概要：普遍余錐全体から図式への射影は写像空間で充満忠実であり、h 上でも射を忠実に比較できる。
方針：相対始対象の正次元境界充填を写像空間の trivial Kan fibration へ移す。
規約：全ての図式の余極限の存在を要求しない。
使われ方：S4 の普遍余錐間の射の選択独立性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対始対象全体から基底への射影は充満忠実。
方針：正次元の全境界の持ち上げと、全部分圏の quasicategory 性を使う。
規約：元と基底は quasicategory、射に追加のファイブレーション仮定なし。
使われ方：普遍余錐の射影への適用。 -/
lemma relativeInitialProjection_isFullyFaithful {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) :
    IsFullyFaithful (relativeInitialProjection p) := by
  have : Quasicategory (relativeInitialVertices p : SSet.{u}) :=
    fullSubcomplexOnVertices_quasicategory _ _
  exact isFullyFaithful_of_boundary_succ (relativeInitialProjection p)
    (relativeInitialProjection_hasLiftingProperty_boundary p)

/-- 概要：普遍余錐全体から図式への射影は写像空間で充満忠実。
方針：余錐の制限の相対始対象の射影に一般補題を適用する。
規約：値域のみ quasicategory、図式の形状は任意。
使われ方：余極限対象の射の比較。 -/
lemma colimitCoconeProjection_isFullyFaithful (K X : SSet.{u}) [Quasicategory X] :
    IsFullyFaithful (colimitCoconeProjection K X) :=
  relativeInitialProjection_isFullyFaithful (coconeRestriction K X)

/-- 概要：普遍余錐の射影は h 上で充満忠実な関手を与える。
方針：写像空間の充満忠実性を Hom の全単射へ移す。
規約：全ての図式の余極限の存在は不要。
使われ方：普遍余錐間の射の選択の比較。 -/
def colimitCoconeProjectionHoFullyFaithful (K X : SSet.{u}) [Quasicategory X] :
    (hoFunctor.map (colimitCoconeProjection K X)).toFunctor.FullyFaithful :=
  (colimitCoconeProjection_isFullyFaithful K X).toHoFullyFaithful

/-- 概要：普遍余錐間の h の射は、図式へ射影した射が一致すれば等しい。
方針：h の射影関手の忠実性を使う。
規約：同じ二つの普遍余錐を始点・終点とする射。
使われ方：図式の比較を固定した余極限間の射の選択独立性。 -/
lemma colimitCoconeProjection_ho_map_injective {K X : SSet.{u}} [Quasicategory X]
    {a b : hoFunctor.obj (colimitCocones K X)} {f g : a ⟶ b}
    (h : (hoFunctor.map (colimitCoconeProjection K X)).toFunctor.map f =
      (hoFunctor.map (colimitCoconeProjection K X)).toFunctor.map g) : f = g :=
  (colimitCoconeProjectionHoFullyFaithful K X).map_injective h

end SerrePositivity.InfinityCategories
