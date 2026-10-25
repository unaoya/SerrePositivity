module
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
/-!
概要：Maurer–Cartan 方程式を満たす次数一 cochain による、非有界複体の微分変更。
方針：元の微分との交換子と追加 cochain の二乗を合わせて二乗零を証明する。
規約：追加 cochain の閉性と二乗零を別々に要求せず、既存の perturbComplex は変更しない。
使われ方：D-8 c2 の coherent dg 図式の全高次成分を含む余極限複体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R] (K : Complex R) (θ : Cochain K K 1)

lemma maurerCartanPerturbedDifferential_squared
    (hθ : δ 1 2 θ + θ.comp θ (show (1 : ℤ) + 1 = 2 from rfl) = 0) (i : ℤ) :
    (K.d i (i + 1) + θ.v i (i + 1) rfl) ≫
      (K.d (i + 1) (i + 1 + 1) + θ.v (i + 1) (i + 1 + 1) rfl) = 0 := by
  have h := congrArg (fun f : Cochain K K 2 => f.v i (i + 1 + 1) (by omega)) hθ
  rw [Cochain.add_v, δ_v 1 2 (by omega) θ i (i + 1 + 1) (by omega) (i + 1) (i + 1)
    (by omega) rfl, show (2 : ℤ).negOnePow = 1 by decide, one_smul,
    Cochain.comp_v θ θ _ i (i + 1) (i + 1 + 1) rfl rfl, Cochain.zero_v] at h
  rw [add_comp, comp_add, comp_add, K.d_comp_d, zero_add]
  simpa only [add_assoc, add_comm, add_left_comm] using h

def maurerCartanPerturbComplex
    (hθ : δ 1 2 θ + θ.comp θ (show (1 : ℤ) + 1 = 2 from rfl) = 0) : Complex R :=
  CochainComplex.of K.X (fun i => K.d i (i + 1) + θ.v i (i + 1) rfl)
    (maurerCartanPerturbedDifferential_squared K θ hθ)

@[simp] lemma maurerCartanPerturbComplex_X
    (hθ : δ 1 2 θ + θ.comp θ (show (1 : ℤ) + 1 = 2 from rfl) = 0) (i : ℤ) :
    (maurerCartanPerturbComplex K θ hθ).X i = K.X i := rfl

@[simp] lemma maurerCartanPerturbComplex_d
    (hθ : δ 1 2 θ + θ.comp θ (show (1 : ℤ) + 1 = 2 from rfl) = 0) (i : ℤ) :
    (maurerCartanPerturbComplex K θ hθ).d i (i + 1) =
      K.d i (i + 1) + θ.v i (i + 1) rfl :=
  CochainComplex.of_d K.X (fun j => K.d j (j + 1) + θ.v j (j + 1) rfl) i

end SerrePositivity.DifferentialGraded
