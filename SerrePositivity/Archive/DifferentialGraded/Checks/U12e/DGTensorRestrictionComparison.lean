module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.DifferentialGraded.Tensor.ResolvedRestriction
public import Mathlib.Data.ZMod.Basic

/-! # dg関手に沿うtensor比較の自然性・合成整合性と代表加群での検査

## 概要
dg関手に沿うtensor比較の自然性・合成整合性と代表加群での検査。

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
universe u v w z
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BalancedTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

-- 任意可換環・独立対象宇宙・任意次数で、元と符号を保つ実際の比較。
example (M : RightModule A E) (N : LeftModule A E) (x : D)
    {r s n : ℤ} (m : (M.obj (.op (F.obj x))).X r) (t : (N.obj (F.obj x)).X s)
    (hn : r + s = n) :
    (restrictionComparison A D E F M N).f n
      (element A D (restrictModule A D E F.op M) (F.comp N) x m t hn) =
        element A E M N (F.obj x) m t hn :=
  restrictionComparison_element A D E F M N x m t hn

example (N : LeftModule A E) {M M' : ModuleCategory A E} (f : M ⟶ M') :
    (moduleRestriction A D E F.op ⋙ rightTensorFunctor A D (F.comp N)).map f ≫
        (restrictionTensorComparison A D E F N).app M' =
      (restrictionTensorComparison A D E F N).app M ≫ (rightTensorFunctor A E N).map f :=
  (restrictionTensorComparison A D E F N).naturality f

-- 準同値の本質的全射性は、この代表加群での検査には不要。
example (hF : HomQuasiIso F) (d : D) (N : LeftModule A E)
    (hN : leftModuleRelativeKFlat A D (F.comp N)) :
    QuasiIso (restrictionComparison A D E F (representable A (F.obj d)) N) :=
  restrictionComparison_representable_quasiIso A D E F hF d N hN

example (T : Type z) [DGCategory A T] [Small.{u} T] (G : DGFunctor A E T)
    (M : RightModule A T) (N : LeftModule A T) :
    (restrictionComparisonCompIso A D E T F G M N).hom ≫
        restrictionComparison A D T (F.comp G) M N =
      restrictionComparison A D E F (restrictModule A E T G.op M) (G.comp N) ≫
        restrictionComparison A E T G M N := restrictionComparison_comp A D E T F G M N

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] (F : DGFunctor (ZMod 2) X Y) (hF : HomQuasiIso F)
    (x : X) (N : LeftModule (ZMod 2) Y)
    (hN : leftModuleRelativeKFlat (ZMod 2) X (F.comp N)) :
    QuasiIso (restrictionComparison (ZMod 2) X Y F (representable (ZMod 2) (F.obj x)) N) :=
  restrictionComparison_representable_quasiIso (ZMod 2) X Y F hF x N hN

namespace SerrePositivity.DifferentialGraded.BalancedTensor
#print axioms restrictionComparison
#print axioms ι_restrictionComparison
#print axioms restrictionComparison_element
#print axioms restrictionComparison_desc
#print axioms rightAction_restrict_family
#print axioms leftAction_restrict_family
#print axioms restrictionComparison_naturality
#print axioms rightAction_restrict_comp
#print axioms leftAction_restrict_comp
#print axioms restrictionComparisonCompIso
#print axioms ι_restrictionComparisonCompIso_hom
#print axioms ι_restrictionComparisonCompIso_inv
#print axioms restrictionComparison_comp
#print axioms restrictionTensorComparison
#print axioms restrictionTensorComparison_app
#print axioms representableRestrictionTensorMap
#print axioms ι_representableRestrictionTensorMap
#print axioms representableRestrictionTensorMap_comparison_yoneda
#print axioms representableRestrictionTensorMap_quasiIso
#print axioms restrictionComparison_representable_quasiIso
end SerrePositivity.DifferentialGraded.BalancedTensor
