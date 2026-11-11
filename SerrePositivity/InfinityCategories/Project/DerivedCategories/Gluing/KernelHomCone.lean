module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelHomCochain

/-! 右加群 Hom の標準円錐から、同じ加群円錐の通常 kernel tensor 像への作用。 -/
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
  {N N' : ModuleCategory R D} (f : N ⟶ N')
local notation "T" => ForgetEnrichment.of (Complex R) (representable R X.right)
local notation "r" => eHomWhiskerLeft (Complex R) T f
local notation "K" => ForgetEnrichment.to (Complex R) (moduleCone R D f)
local notation "F" => Morita.kernelTensor R D C M

/-- 標準右 Hom 円錐を、元の円錐の同じ通常 tensor 像へ送る実鎖写像。 -/
def dgGluingKernelHomConeAction : mappingCone r ⟶
    moduleHom R C (representable R X.left) ((F).obj K) :=
  moduleHomConeComparison R D T f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X K

/-- 右包含は実 tensor 像の閉包含への作用として回収できる。 -/
lemma dgGluingKernelHomConeAction_inr :
    mappingCone.inr r ≫ dgGluingKernelHomConeAction R C D M X f =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X N' ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (representable R X.left))
        ((F).onClosed.map (moduleConeInr R D f)) := by
  rw [dgGluingKernelHomConeAction, moduleHomConeComparison_inr_assoc]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction_postcompose R C D M X (moduleConeInr R D f)

/-- 次数 −1 の包含も、実 tensor の全 Hom 写像で送った同じ包含を回収する。 -/
lemma dgGluingKernelHomConeAction_inl :
    (mappingCone.inl r).comp
      (Cochain.ofHom (dgGluingKernelHomConeAction R C D M X f)) (add_zero (-1)) =
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X N)).comp
      ((modulePostcompositionMap R C (representable R X.left)
        ((F).obj (ForgetEnrichment.to (Complex R) N)) ((F).obj K)).f (-1)
          (dgModuleFunctorConeInl R D C F f)) (zero_add (-1)) := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction_coneInl R C D M X f
  apply Cochain.ext
  intro q n hn
  have hv := Cochain.congr_v he q n hn
  simpa only [dgGluingKernelHomConeAction, moduleHomConeComparison,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.comp_f,
    mappingCone.inl_v_desc_f_assoc] using hv

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
