module

public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFunctorHom
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantFunctor

/-!
# 全区間族の前合成方程式の同じ関手による像

概要：指定射の前合成を表す全族方程式は、元の関手の同じ射の像で保たれる。
方針：全族の後合成公式と定値射の後合成の自然性を合成する。
規約：任意パラメータ K と元の関手 F を保つ。
使われ方：全複体の自由単位の全族を同じ半自由分解関手で送る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

lemma intervalFamilyFunctorMap_precompose {K C D : SSet.{u}} (F : C ⟶ D)
    {x' x y : C _⦋0⦌} (γ : (HomotopyCategory.mk x' : hoFunctor.obj C) ⟶ HomotopyCategory.mk x)
    (f : K ⟶ intervalMappingSpace x' y) (g : K ⟶ intervalMappingSpace x y)
    (h : intervalFamilyHom f = constantFunctorHomMap K γ ≫ intervalFamilyHom g) :
    intervalFamilyHom (f ≫ intervalFunctorMap F x' y) =
    constantFunctorHomMap K ((hoFunctor.map F).toFunctor.map γ) ≫
      intervalFamilyHom (g ≫ intervalFunctorMap F x y) := by
  rw [intervalFunctorMap_familyHom, h, CategoryTheory.Functor.map_comp,
    intervalFunctorMap_familyHom, ← constantFunctorHomMap_postcomp K F γ]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.EInfinity.ComplexLimits
