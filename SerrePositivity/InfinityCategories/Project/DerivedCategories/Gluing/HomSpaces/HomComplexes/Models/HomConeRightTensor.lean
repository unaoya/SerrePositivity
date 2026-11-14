module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.YonedaConeCanonical
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.Kernels.KernelHomCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Actions.HomConeRightAction

/-! 元の右 Hom 円錐を同じ Yoneda 円錐の通常 kernel tensor 像へ送り、両包含を回収する。 -/
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
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "rf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M)) f
local notation "yf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (dgYoneda R D)) rf
local notation "K" => ForgetEnrichment.to (Complex R) (moduleCone R D yf)
local notation "F" => Morita.kernelTensor R D C M
local notation "r" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightArrow R C D M X Y Z f

/-- 右 Hom 円錐を、同じ Yoneda 円錐の通常 tensor 像への全 Hom へ送る。 -/
def dgGluingHomConeRightTensorAction : mappingCone r ⟶
    moduleHom R C (representable R X.left) ((F).obj K) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightModuleIso R C D M X Y Z f).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X K

/-- 元の右 Hom 円錐の写像は、標準 Hom 円錐からの kernel 作用そのもの。 -/
lemma dgGluingHomConeRightTensorAction_canonical :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeMap R D X.right Y.right Z.right rf).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomConeAction R C D M X yf =
    dgGluingHomConeRightTensorAction R C D M X Y Z f := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomConeAction, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeIso_canonical]
  rfl

/-- 右包含の tensor 作用は、元の右代表 Hom と実 tensor の閉包含の後合成。 -/
lemma dgGluingHomConeRightTensorAction_inr :
    mappingCone.inr r ≫ dgGluingHomConeRightTensorAction R C D M X Y Z f =
    yonedaHom R D X.right Z.right ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X (representable R Z.right) ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (representable R X.left))
        ((F).onClosed.map (moduleConeInr R D yf)) := by
  change mappingCone.inr r ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeIso R D X.right Y.right Z.right rf).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X K) = _
  erw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeIso_inr R D X.right Y.right Z.right rf,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction_postcompose R C D M X (moduleConeInr R D yf)]
  rfl

/-- 左包含の tensor 作用も、同じ全 Hom の次数 −1 包含から回収する。 -/
lemma dgGluingHomConeRightTensorAction_inl :
    (mappingCone.inl r).comp
      (Cochain.ofHom (dgGluingHomConeRightTensorAction R C D M X Y Z f)) (add_zero (-1)) =
    (Cochain.ofHom (yonedaHom R D X.right Y.right ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X (representable R Y.right))).comp
        ((modulePostcompositionMap R C (representable R X.left)
          ((F).obj (representable R Y.right)) ((F).obj K)).f (-1)
            (dgModuleFunctorConeInl R D C F yf)) (zero_add (-1)) := by
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeIso_inl R D X.right Y.right Z.right rf
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction_coneInl R C D M X yf
  apply Cochain.ext
  intro q n hn
  have hsq := Cochain.congr_v hs q n hn
  have htq := Cochain.congr_v ht q n hn
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    Cochain.zero_cochain_comp_v] at hsq htq
  simp only [dgGluingHomConeRightTensorAction, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightModuleIso,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.comp_f,
    Cochain.zero_cochain_comp_v]
  erw [← Category.assoc, hsq, Category.assoc, htq]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
