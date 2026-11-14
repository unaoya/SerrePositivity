module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.Kernels.KernelHomComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.ModulePostAction
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-! kernel 作用の全次数での自然性を cochain に転置し、円錐の左包含へ適用する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 任意次数の後合成を kernel 作用の前後に移せる。 -/
lemma dgGluingKernelHomAction_cochain (N N' : RightModule R D) (p : ℤ)
    (g : (moduleHom R D N N').X p) :
    ((modulePostcompositionMap R D (representable R X.right) N N').f p g).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X N')) (add_zero p) =
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X N)).comp
      ((modulePostcompositionMap R C (representable R X.left)
        ((Morita.kernelTensor R D C M).obj N) ((Morita.kernelTensor R D C M).obj N')).f p
          ((Morita.kernelTensor R D C M).map N N' |>.f p g)) (zero_add p) := by
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply,
    modulePostcompositionMap_apply, modulePostcompositionMap_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction_compose R C D M X g t hn

/-- 特に右 Hom cone の次数 −1 包含は、同じ tensor の全 Hom 像で与えられる。 -/
lemma dgGluingKernelHomAction_coneInl {N N' : ModuleCategory R D} (f : N ⟶ N') :
    (moduleHomConeLeftCochain R D
      (ForgetEnrichment.of (Complex R) (representable R X.right)) f).comp
        (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X
          (ForgetEnrichment.to (Complex R) (moduleCone R D f)))) (add_zero (-1)) =
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X N)).comp
      ((modulePostcompositionMap R C (representable R X.left)
        ((Morita.kernelTensor R D C M).obj (ForgetEnrichment.to (Complex R) N))
        ((Morita.kernelTensor R D C M).obj
          (ForgetEnrichment.to (Complex R) (moduleCone R D f)))).f (-1)
            (dgModuleFunctorConeInl R D C (Morita.kernelTensor R D C M) f)) (zero_add (-1)) :=
  dgGluingKernelHomAction_cochain R C D M X _ _ (-1) (moduleConeInlElement R D f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
