module

public import SerrePositivity.EInfinity.CosimplicialNormalization.DualProjector
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies

/-!
# 同じDold–Kan射影と元の全codegeneracy核の照合

Dold–Kanの正規化とBerger–Fresse §2.2、M14 L21、報告 §399。
元のσ消滅とPInfty+QInfty=1を反対圏から運ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.CosimplicialNormalization
open CategoryTheory HomologicalComplex AlgebraicTopology Opposite
open scoped Simplicial DoldKan
variable (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat.{u} A))

/-- 同じ移した射影の像は元の全σの核に入る（Dold–Kan）。 -/
lemma cofaceProjectorNat_mem (q : ℕ) (a : X.obj ⦋q⦌) :
    (cofaceProjectorNat A X).f q a ∈ normalizedSubmodule A X q := by
  cases q with
  | zero => exact Submodule.mem_top
  | succ q =>
    apply (mem_normalized_succ A X q _).mpr
    intro i
    have H := congrArg Quiver.Hom.unop (DoldKan.σ_comp_PInfty (dualSimplicial A X) i)
    change ((DoldKan.PInfty (X := dualSimplicial A X)).f (q + 1)).unop ≫ X.σ i = 0 at H
    rw [cofaceProjectorNat_f]
    exact ConcreteCategory.congr_hom H a

/-- 元の全σ核上では同じ射影は恒等（Dold–Kan）。 -/
lemma cofaceProjectorNat_normalized (q : ℕ) (a : normalizedSubmodule A X q) :
    (cofaceProjectorNat A X).f q a.val = a.val := by
  let inclusion : ModuleCat.of A (normalizedSubmodule A X q) ⟶ X.obj ⦋q⦌ :=
    ModuleCat.ofHom (normalizedSubmodule A X q).subtype
  let f : (dualSimplicial A X).obj (op ⦋q⦌) ⟶ op (ModuleCat.of A (normalizedSubmodule A X q)) :=
    inclusion.op
  have hf : DoldKan.DegeneraciesVanish (X := dualSimplicial A X) (n := q) f := by
    cases q with
    | zero => exact (DoldKan.degeneraciesVanish_zero_iff_true f).mpr trivial
    | succ q =>
      apply (DoldKan.degeneraciesVanish_succ_iff (X := dualSimplicial A X) (n := q) f).mpr
      intro i
      apply Quiver.Hom.unop_inj
      change inclusion ≫ X.σ i = 0
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro b
      exact (mem_normalized_succ A X q b.val).mp b.property i
  have hQ := (DoldKan.degeneraciesVanish_iff_QInfty_f_comp
    (X := dualSimplicial A X) (n := q) f).mp hf
  have HP := congrArg (fun g => g ≫ f)
    (DoldKan.PInfty_f_add_QInfty_f (X := dualSimplicial A X) q)
  rw [Preadditive.add_comp, hQ, add_zero, Category.id_comp] at HP
  have H := congrArg Quiver.Hom.unop HP
  change inclusion ≫ ((DoldKan.PInfty (X := dualSimplicial A X)).f q).unop = inclusion at H
  rw [cofaceProjectorNat_f]
  exact ConcreteCategory.congr_hom H a

end SerrePositivity.EInfinity.CosimplicialNormalization
