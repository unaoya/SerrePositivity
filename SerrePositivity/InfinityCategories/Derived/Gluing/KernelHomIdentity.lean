module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelHomProjections

/-! kernel Hom 比較は、任意パラメータの第三 cochain と元の閉単位を保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y : DGGluingObject R C D M)
local notation "F" => Morita.kernelTensor R D C M
local notation "B" => dgGluingKernelObject R C D M X
local notation "T" => dgGluingKernelObject R C D M Y

/-- 任意パラメータからの比較 cochain は、元の同じ比較 cochain の列同型による像。 -/
lemma dgGluingKernelHomComparison (K : Complex R) (f : K ⟶ dgGluingHomComplex R C D M X Y) :
    dgFunctorCommaHomComparison R (RightModule R D) (RightModule R C) F B T K
      (f ≫ (dgGluingKernelHomIso R C D M X Y).hom) =
    (dgGluingHomComparison R C D M X Y K f).comp
      (Cochain.ofHom (dgGluingKernelHomTargetIso R C D M X Y).hom) (add_zero (-1)) := by
  apply Cochain.ext
  intro p q hpq
  simp only [dgFunctorCommaHomComparison, dgGluingHomComparison,
    Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    HomologicalComplex.comp_f]
  have he := dgGluingKernelHomIso_primitive_v R C D M X Y p q hpq
  change _ = f.f p ≫ (dgGluingHomPrimitive R C D M X Y).v p q hpq ≫
    (dgGluingKernelHomTargetIso R C D M X Y).hom.f q
  erw [Category.assoc, he]

omit Y in
/-- 元の閉単位を kernel Hom 比較で送ると、同じ kernel 表示の閉単位に厳密に一致。 -/
lemma dgGluingKernelHomIso_identity :
    dgGluingIdentity R C D M X ≫ (dgGluingKernelHomIso R C D M X X).hom =
    dgFunctorCommaIdentity R (RightModule R D) (RightModule R C) F B := by
  apply dgFunctorCommaHom_ext R (RightModule R D) (RightModule R C) F B B (𝟙_ (Complex R))
  · rw [Category.assoc, dgGluingKernelHomIso_right, ← Category.assoc,
      dgGluingIdentity_right, dgFunctorCommaIdentity_source]
    exact (dgYoneda R D).map_id X.right
  · rw [Category.assoc, dgGluingKernelHomIso_left, ← Category.assoc,
      dgGluingIdentity_left, dgFunctorCommaIdentity_replacement]
    exact (dgYoneda R C).map_id X.left
  · rw [dgGluingKernelHomComparison, dgGluingIdentity_comparison,
      Cochain.zero_comp, dgFunctorCommaIdentity_comparison]

end SerrePositivity.InfinityCategories
