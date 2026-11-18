module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Normalization.DualProjector
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
namespace SerrePositivity.CosimplicialNormalization
open _root_.CategoryTheory _root_.HomologicalComplex _root_.AlgebraicTopology _root_.Opposite
open scoped _root_.Simplicial _root_.DoldKan _root_.AlgebraicTopology.DoldKan
variable (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat.{u} A))

/-- 同じ移した射影の像は元の全σの核に入る（Dold–Kan）。 -/
lemma cofaceProjectorNat_mem (q : ℕ) (a : X.obj ⦋q⦌) :
    (_root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat A X).f q a ∈ _root_.SerrePositivity.CosimplicialNormalization.normalizedSubmodule A X q := by
  cases q with
  | zero => exact Submodule.mem_top
  | succ q =>
    apply (_root_.SerrePositivity.CosimplicialNormalization.mem_normalized_succ A X q _).mpr
    intro i
    have H := congrArg Quiver.Hom.unop (DoldKan.σ_comp_PInfty (_root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X) i)
    change ((DoldKan.PInfty (X := _root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X)).f (q + 1)).unop ≫ X.σ i = 0 at H
    rw [_root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat_f]
    exact ConcreteCategory.congr_hom H a

/-- 元の全σ核上では同じ射影は恒等（Dold–Kan）。 -/
lemma cofaceProjectorNat_normalized (q : ℕ) (a : _root_.SerrePositivity.CosimplicialNormalization.normalizedSubmodule A X q) :
    (_root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat A X).f q a.val = a.val := by
  let inclusion : ModuleCat.of A (_root_.SerrePositivity.CosimplicialNormalization.normalizedSubmodule A X q) ⟶ X.obj ⦋q⦌ :=
    ModuleCat.ofHom (_root_.SerrePositivity.CosimplicialNormalization.normalizedSubmodule A X q).subtype
  let f : (_root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X).obj (op ⦋q⦌) ⟶ op (ModuleCat.of A (_root_.SerrePositivity.CosimplicialNormalization.normalizedSubmodule A X q)) :=
    inclusion.op
  have hf : DoldKan.DegeneraciesVanish (X := _root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X) (n := q) f := by
    cases q with
    | zero => exact (DoldKan.degeneraciesVanish_zero_iff_true f).mpr trivial
    | succ q =>
      apply (DoldKan.degeneraciesVanish_succ_iff (X := _root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X) (n := q) f).mpr
      intro i
      apply Quiver.Hom.unop_inj
      change inclusion ≫ X.σ i = 0
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro b
      exact (_root_.SerrePositivity.CosimplicialNormalization.mem_normalized_succ A X q b.val).mp b.property i
  have hQ := (DoldKan.degeneraciesVanish_iff_QInfty_f_comp
    (X := _root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X) (n := q) f).mp hf
  have HP := congrArg (fun g => g ≫ f)
    (DoldKan.PInfty_f_add_QInfty_f (X := _root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X) q)
  rw [Preadditive.add_comp, hQ, add_zero, Category.id_comp] at HP
  have H := congrArg Quiver.Hom.unop HP
  change inclusion ≫ ((DoldKan.PInfty (X := _root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X)).f q).unop = inclusion at H
  rw [_root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat_f]
  exact ConcreteCategory.congr_hom H a

end SerrePositivity.CosimplicialNormalization
