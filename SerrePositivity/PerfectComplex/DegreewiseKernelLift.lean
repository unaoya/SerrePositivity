module

public import SerrePositivity.PerfectComplex.IdempotentDecomposition
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Lifting graded maps into a cochain kernel -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Evaluation preserves exactness of the kernel sequence, so a graded map can be lifted. -/
def cochainKernelLiftX {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (n : ℤ) {W : ModuleCat.{u} R} (v : W ⟶ P.X n)
    (hv : v ≫ f.f n = 0) : W ⟶ (kernel f).X n := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  let S' := S.map (eval _ _ n)
  have : Mono S'.f := by
    change Mono ((kernel.ι f).f n)
    infer_instance
  have he : S'.Exact := (ShortComplex.exact_kernel f).map (eval _ _ n)
  exact he.lift v hv

@[reassoc]
lemma cochainKernelLiftX_inclusion {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (n : ℤ) {W : ModuleCat.{u} R} (v : W ⟶ P.X n)
    (hv : v ≫ f.f n = 0) :
    cochainKernelLiftX f n v hv ≫ (kernel.ι f).f n = v := by
  dsimp [cochainKernelLiftX]
  exact Fork.IsLimit.lift_ι _

lemma cochainBiprodDegree_hom_ext (A B : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) {W : ModuleCat.{u} R} {f g : W ⟶ (A ⊞ B).X n}
    (hf : f ≫ (biprod.fst : A ⊞ B ⟶ A).f n = g ≫ (biprod.fst : A ⊞ B ⟶ A).f n)
    (hg : f ≫ (biprod.snd : A ⊞ B ⟶ B).f n = g ≫ (biprod.snd : A ⊞ B ⟶ B).f n) : f = g := by
  apply (isLimitOfPreserves (eval (ModuleCat.{u} R) (.up ℤ) n)
    (BinaryBiproduct.isLimit A B)).hom_ext
  rintro ⟨j⟩
  cases j
  · exact hf
  · exact hg

end SerrePositivity
