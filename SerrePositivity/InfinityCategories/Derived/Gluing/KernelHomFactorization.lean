module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaKernelFunctor

/-! native/kernel Hom 同型は、元の代表加群表示と comma kernel 比較の合成そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y : DGGluingObject R C D M)
local notation "F" => Morita.kernelTensor R D C M
local notation "OX" => dgGluingCommaObject R C D M X
local notation "OY" => dgGluingCommaObject R C D M Y

/-- 係数の列比較は、元の Yoneda 逆射と列同型の後合成を順に行ったもの。 -/
lemma dgGluingKernelHomTargetIso_factorization :
    (dgYonedaIso R X.left (M.rightAt Y.right)).inv ≫
      (dgGluingCommaKernelTargetIso R C D M OX OY).hom =
    (dgGluingKernelHomTargetIso R C D M X Y).hom := by
  apply (cancel_mono (dgYonedaIso R X.left ((F).obj (representable R Y.right))).hom).1
  simp only [dgGluingCommaKernelTargetIso_hom, dgGluingKernelHomTargetIso,
    Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := dgGluingYoneda_postcompose R C X.left
    (dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).inv
  erw [hn]
  rw [← Category.assoc]
  erw [Iso.inv_hom_id, Category.id_comp]

/-- native/kernel Hom 比較は、同じ二射影・第三 cochain を持つ二比較の合成。 -/
lemma dgGluingKernelHomIso_factorization :
    (dgGluingHomRepresentableIso R C D M X Y).hom ≫
      (dgGluingCommaKernelHomIso R C D M OX OY).hom =
    (dgGluingKernelHomIso R C D M X Y).hom := by
  apply dgFunctorCommaHom_ext R (RightModule R D) (RightModule R C) F
    (dgGluingKernelObject R C D M X) (dgGluingKernelObject R C D M Y)
    (dgGluingHomComplex R C D M X Y)
  · rw [Category.assoc]
    erw [dgGluingCommaKernelHomIso_source R C D M OX OY]
    rw [← Category.assoc,
      dgGluingHomRepresentableIso_right, dgGluingKernelHomIso_right]
    rfl
  · rw [Category.assoc]
    erw [dgGluingCommaKernelHomIso_replacement R C D M OX OY]
    rw [dgGluingHomRepresentableIso_left, dgGluingKernelHomIso_left]
  · erw [dgGluingCommaKernelHomComparison R C D M OX OY]
    change ((Cochain.ofHom (dgGluingHomRepresentableIso R C D M X Y).hom).comp
      (dgFunctorCommaPrimitive R D (RightModule R C) M.toFunctor OX OY)
      (zero_add (-1))).comp
      (Cochain.ofHom (dgGluingCommaKernelTargetIso R C D M OX OY).hom)
      (add_zero (-1)) = _
    rw [dgGluingHomRepresentableIso_primitive,
      Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
      dgGluingKernelHomTargetIso_factorization]
    exact (dgGluingKernelHomIso_primitive R C D M X Y).symm

end SerrePositivity.InfinityCategories
