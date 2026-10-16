module
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-! # 始域の微分変更と次数0 cochainからのchain map -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Preadditive HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- δf=θfを満たすcochainは、始域の微分をd+θへ変えるとchain mapとなる。 -/
def perturbSourceMap (K L : Complex A) (θ : Cochain K K 1) (hθ : δ 1 2 θ = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0)
    (f : Cochain K L 0) (hf : δ 0 1 f = θ.comp f (add_zero 1)) :
    perturbComplex K θ hθ hθθ ⟶ L :=
  CochainComplex.ofHom (fun i => f.v i i (add_zero i)) (fun i => by
    have h := congrArg (fun z : Cochain K L 1 => z.v i (i + 1) rfl) hf
    rw [δ_zero_cochain_v, Cochain.comp_zero_cochain_v] at h
    rw [perturbComplex_d, add_comp]
    simpa only [add_comm] using (sub_eq_iff_eq_add).1 h)

lemma perturbSourceMap_f (K L : Complex A) (θ : Cochain K K 1) (hθ : δ 1 2 θ = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0)
    (f : Cochain K L 0) (hf : δ 0 1 f = θ.comp f (add_zero 1)) (i : ℤ) :
    (perturbSourceMap K L θ hθ hθθ f hf).f i = f.v i i (add_zero i) := rfl

end SerrePositivity.DifferentialGraded
