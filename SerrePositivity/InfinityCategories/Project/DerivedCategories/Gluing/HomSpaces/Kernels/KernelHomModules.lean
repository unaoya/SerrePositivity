module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.KernelComparisonFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Size
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Endomorphism.Module
public import SerrePositivity.DifferentialGraded.Bimodule.Basic

/-! kernel comma の各対象への Hom を、native gluing 上の全 dg 自然な右加群へ束ねる。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory Opposite DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonFunctor R C D M

/-- 標準シフト対象も値に取れる、native 入力だけに制限した同じ右 Hom 加群。 -/
def dgGluingKernelHomModule
    (Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
      (Morita.kernelTensor R D C M)) : RightModule R G :=
  restrictModule R G E (p).op (representable R Z)

/-- kernel Hom の全次数後合成を、同じ制限加群間のパラメータ自然族へ移す。 -/
def dgGluingKernelHomModuleParam
    (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
      (Morita.kernelTensor R D C M)) :
    ModuleParamTrans R G (homObject R E Y Z)
      (dgGluingKernelHomModule R C D M Y) (dgGluingKernelHomModule R C D M Z) :=
  moduleRestrictionParam R G E (p).op (yonedaExtension R Y (representable R Z) (𝟙 _))

/-- 大きい kernel comma に Small 仮定を置かない、native gluing 上の制限 Yoneda。 -/
def dgGluingKernelHomModuleFunctor : DGFunctor R E (RightModule R G) :=
  Bimodule.ofParamTrans R G E (dgGluingKernelHomModule R C D M)
    (dgGluingKernelHomModuleParam R C D M)
    (by
      intro Z c
      change eId (Complex R) Z ≫
        yonedaExtensionApp R Z (representable R Z) (𝟙 _) ((p).op.obj c) = _
      rw [endomorphismYonedaApp]
      exact (leftRepresentable R ((p).obj c.unop)).map_id Z)
    (by
      intro X Y Z c
      change eComp (Complex R) X Y Z ≫
        yonedaExtensionApp R X (representable R Z) (𝟙 _) ((p).op.obj c) = _
      rw [endomorphismYonedaApp]
      change eComp (Complex R) X Y Z ≫ (leftRepresentable R ((p).obj c.unop)).map X Z =
        (yonedaExtensionApp R X (representable R Y) (𝟙 _) ((p).op.obj c) ⊗ₘ
          yonedaExtensionApp R Y (representable R Z) (𝟙 _) ((p).op.obj c)) ≫ _
      rw [endomorphismYonedaApp, endomorphismYonedaApp]
      exact (leftRepresentable R ((p).obj c.unop)).map_comp X Y Z)

lemma dgGluingKernelHomModuleFunctor_map_π
    (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
      (Morita.kernelTensor R D C M)) (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (dgGluingKernelHomModuleFunctor R C D M).map Y Z ≫ moduleHomπ R G _ _ X =
      (leftRepresentable R ((p).obj X)).map Y Z :=
  (Bimodule.ofParamTrans_map_π R G E _ _ _ _ Y Z X).trans
    (endomorphismYonedaApp R E ((p).obj X) Y Z)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
