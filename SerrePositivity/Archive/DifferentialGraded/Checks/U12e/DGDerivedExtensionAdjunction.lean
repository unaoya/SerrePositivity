module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import Mathlib.Data.ZMod.Basic

/-! # graph導来延長–制限随伴・自然性・三角恒等式の検査

## 概要
graph導来延長–制限随伴・自然性・三角恒等式の検査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

-- 任意可換環・独立宇宙。元のHomのflatness・有界性は要求しない。
example : dgDerivedExtension A D E F ⊣ dgDerivedRestriction A D E F :=
  dgDerivedExtensionRestrictionAdjunction A D E F

example {X X' : DerivedModuleCategory A D} (f : X ⟶ X') (Y : DerivedModuleCategory A E)
    (φ : (dgDerivedExtension A D E F).obj X' ⟶ Y) :
    dgDerivedExtensionHomEquiv A D E F X Y ((dgDerivedExtension A D E F).map f ≫ φ) =
      f ≫ dgDerivedExtensionHomEquiv A D E F X' Y φ :=
  dgDerivedExtensionHomEquiv_naturality_left A D E F f Y φ

example (X : DerivedModuleCategory A D) {Y Y' : DerivedModuleCategory A E}
    (φ : (dgDerivedExtension A D E F).obj X ⟶ Y) (g : Y ⟶ Y') :
    dgDerivedExtensionHomEquiv A D E F X Y' (φ ≫ g) =
      dgDerivedExtensionHomEquiv A D E F X Y φ ≫ (dgDerivedRestriction A D E F).map g :=
  dgDerivedExtensionHomEquiv_naturality_right A D E F X φ g

example (X : DerivedModuleCategory A D) :
    (dgDerivedExtension A D E F).map ((dgDerivedExtensionUnit A D E F).app X) ≫
      (dgDerivedExtensionCounit A D E F).app ((dgDerivedExtension A D E F).obj X) = 𝟙 _ :=
  dgDerivedExtension_left_triangle A D E F X

example (Y : DerivedModuleCategory A E) :
    (dgDerivedExtensionUnit A D E F).app ((dgDerivedRestriction A D E F).obj Y) ≫
      (dgDerivedRestriction A D E F).map ((dgDerivedExtensionCounit A D E F).app Y) = 𝟙 _ :=
  dgDerivedExtension_right_triangle A D E F Y

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] (F : DGFunctor (ZMod 2) X Y) :
    dgDerivedExtension (ZMod 2) X Y F ⊣ dgDerivedRestriction (ZMod 2) X Y F :=
  dgDerivedExtensionRestrictionAdjunction (ZMod 2) X Y F

namespace SerrePositivity.DifferentialGraded
#print axioms DGFunctor.homotopyAdjunction_homEquiv_map
#print axioms dgProjectiveDerivedExtensionHomEquiv_map
#print axioms dgDerivedRestrictionComputation_inv_naturality
#print axioms dgProjectiveDerivedExtensionHomEquiv_naturality_right
#print axioms dgProjectiveDerivedExtensionHomEquiv_naturality_left
#print axioms dgExtensionHomotopyComputation_naturality
#print axioms dgResolutionDerivedExtensionComputation_naturality
#print axioms dgDerivedExtensionResolutionComputation_canonical
#print axioms dgDerivedExtensionResolutionComputation_inv_naturality
#print axioms dgDerivedExtensionHomEquivOnModules_apply
#print axioms dgDerivedExtensionHomEquivOnModules_naturality_right
#print axioms dgResolutionLift_derived_fac
#print axioms dgResolutionLift_derived_inv_naturality
#print axioms dgDerivedExtensionHomEquivOnModules_naturality_left
#print axioms dgDerivedExtensionHomEquiv_naturality_right
#print axioms dgDerivedExtensionHomEquiv_naturality_left
#print axioms dgDerivedExtensionRestrictionAdjunction
#print axioms dgDerivedExtensionUnit
#print axioms dgDerivedExtensionCounit
#print axioms dgDerivedExtension_left_triangle
#print axioms dgDerivedExtension_right_triangle
end SerrePositivity.DifferentialGraded
