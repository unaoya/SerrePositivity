module
public import SerrePositivity.DifferentialGraded.Tensor.Swap
public import Mathlib.Data.ZMod.Basic

/-! # opposite上のbalanced tensorとの符号付き交換の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Opposite SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BalancedTensor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

-- 族の比較自体はDのsmallnessを使わない。
example (M : RightModule A D) (N : LeftModule A D) (T : Complex A) :
    BalancedFamily A D M N T ≃ BalancedFamily A Dᵒᵖ N.toRightOpposite M.toFunctor T :=
  swapFamilyEquiv A D M N T

example [Small.{u} D] (M : RightModule A D) (N : LeftModule A D) :
    obj A D M N ≅ obj A Dᵒᵖ N.toRightOpposite M.toFunctor := swapIso A D M N

example [Small.{u} D] (M : RightModule A D) (N : LeftModule A D) (x : D)
    (m : (M.obj (op x)).X (-1)) (t : (N.obj x).X 1) :
    (swapHom A D M N).f 0 (element A D M N x m t (by omega)) =
      -(element A Dᵒᵖ N.toRightOpposite M.toFunctor (op x) t m (by omega)) := by
  simpa using swapHom_element A D M N x m t (by omega : -1 + 1 = 0)

example (M : RightModule (ZMod 2) PUnit.{1}) (N : LeftModule (ZMod 2) PUnit.{1}) :
    obj (ZMod 2) PUnit.{1} M N ≅
      obj (ZMod 2) PUnit.{1}ᵒᵖ N.toRightOpposite M.toFunctor := swapIso (ZMod 2) PUnit.{1} M N

#print axioms balancedFamily_element_of_sums
#print axioms leftToRightOpposite_action
#print axioms rightToLeft_action
#print axioms swapFamilyApp
#print axioms swapFamilyApp_element
#print axioms unswapFamilyApp
#print axioms unswapFamilyApp_element
#print axioms swapFamily
#print axioms unswapFamily
#print axioms swapFamilyEquiv
#print axioms swapHom
#print axioms unswapHom
#print axioms ι_swapHom
#print axioms ι_unswapHom
#print axioms swapHom_element
#print axioms unswapHom_element
#print axioms swapIso
