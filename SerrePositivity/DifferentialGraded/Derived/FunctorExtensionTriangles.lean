module
public import SerrePositivity.DifferentialGraded.Derived.RestrictionTriangles
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # graph導来随伴に整合する整数shiftと三角性

## 概要
graph導来随伴に整合する整数shiftと三角性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

local instance : (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance : (dgDerivedRestriction A D E F).IsTriangulated :=
  dgDerivedRestrictionIsTriangulated A D E F
local instance : (dgDerivedRestriction A D E F).Additive := dgDerivedRestriction_additive A D E F

/-- 実際の導来随伴から左関手へ運ぶ、随伴と整合するshift。 -/
@[instance_reducible]
def dgDerivedExtensionCommShift : (dgDerivedExtension A D E F).CommShift ℤ :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).leftAdjointCommShift ℤ

lemma dgDerivedExtensionRestrictionAdjunction_commShift :
    letI := dgDerivedExtensionCommShift A D E F
    (dgDerivedExtensionRestrictionAdjunction A D E F).CommShift ℤ :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).commShift_of_rightAdjoint ℤ

lemma dgDerivedExtensionUnit_commShift :
    letI := dgDerivedExtensionCommShift A D E F
    NatTrans.CommShift (dgDerivedExtensionUnit A D E F) ℤ := by
  let := dgDerivedExtensionCommShift A D E F
  let := dgDerivedExtensionRestrictionAdjunction_commShift A D E F
  unfold dgDerivedExtensionUnit
  infer_instance

lemma dgDerivedExtensionCounit_commShift :
    letI := dgDerivedExtensionCommShift A D E F
    NatTrans.CommShift (dgDerivedExtensionCounit A D E F) ℤ := by
  let := dgDerivedExtensionCommShift A D E F
  let := dgDerivedExtensionRestrictionAdjunction_commShift A D E F
  unfold dgDerivedExtensionCounit
  infer_instance

lemma dgDerivedExtensionIsTriangulated :
    letI := dgDerivedExtensionCommShift A D E F
    (dgDerivedExtension A D E F).IsTriangulated := by
  let := dgDerivedExtensionCommShift A D E F
  let := dgDerivedExtensionRestrictionAdjunction_commShift A D E F
  exact (dgDerivedExtensionRestrictionAdjunction A D E F).isTriangulated_leftAdjoint

lemma dgDerivedExtension_additive : (dgDerivedExtension A D E F).Additive :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).left_adjoint_additive

end SerrePositivity.DifferentialGraded
