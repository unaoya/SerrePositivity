module

public import SerrePositivity.EInfinity.BarrattEccles.Contraction
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# 標準単体の正規化鎖の実収縮

概要：各標準単体の追加退化を正規化 Moore 複体の鎖ホモトピー同値へ移す。
方針：既存の Moore・交代面鎖比較と、同じ単体の追加退化を合成する。
規約：任意可換環で構成し、群同変性や標数の仮定を課さない。
使われ方：正規化単体テンソルの augmentation と弱同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A]

def normalizedSimplexChainContraction (n : SimplexCategory) : HomotopyEquiv
    ((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
      ((linearization A).obj (SSet.stdSimplex.obj n)))
    ((ChainComplex.single₀ (ModuleCat A)).obj (𝟙_ (ModuleCat A))) :=
  AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex.trans
    (((SSet.Augmented.StandardSimplex.extraDegeneracy n).map
      (uliftFunctor.{u, 0} ⋙ ModuleCat.free A)).homotopyEquiv.trans
        (HomotopyEquiv.ofIso ((ChainComplex.single₀ (ModuleCat A)).mapIso
          ((uliftFunctor.{u, 0} ⋙ ModuleCat.free A).mapIso Limits.Types.terminalIso ≪≫
            singletonFreeIso A))))

end SerrePositivity.ComplexLimits
