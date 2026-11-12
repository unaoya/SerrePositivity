module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaKernelFunctor

/-! native/kernel Hom 同型は、元の代表加群表示と comma kernel 比較の合成そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "F" => Morita.kernelTensor R D C M
local notation "OX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X
local notation "OY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y

/-- 係数の列比較は、元の Yoneda 逆射と列同型の後合成を順に行ったもの。 -/
lemma dgGluingKernelHomTargetIso_factorization :
    (dgYonedaIso R X.left (M.rightAt Y.right)).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelTargetIso R C D M OX OY).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomTargetIso R C D M X Y).hom := by
  apply (cancel_mono (dgYonedaIso R X.left ((F).obj (representable R Y.right))).hom).1
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelTargetIso_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomTargetIso,
    Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_postcompose R C X.left
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).inv
  erw [hn]
  rw [← Category.assoc]
  erw [Iso.inv_hom_id, Category.id_comp]

/-- native/kernel Hom 比較は、同じ二射影・第三 cochain を持つ二比較の合成。 -/
lemma dgGluingKernelHomIso_factorization :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso R C D M OX OY).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M X Y).hom := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R (RightModule R D) (RightModule R C) F
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y)
  · rw [Category.assoc]
    erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso_source R C D M OX OY]
    rw [← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_right, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso_right]
    rfl
  · rw [Category.assoc]
    erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso_replacement R C D M OX OY]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_left, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso_left]
  · erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomComparison R C D M OX OY]
    change ((Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R D (RightModule R C) M.toFunctor OX OY)
      (zero_add (-1))).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelTargetIso R C D M OX OY).hom)
      (add_zero (-1)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_primitive,
      Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
      dgGluingKernelHomTargetIso_factorization]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso_primitive R C D M X Y).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
