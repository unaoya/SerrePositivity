module
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanPerturbation
/-!
概要：両端を Maurer–Cartan 変形した Hom の全次数微分を計算する。
方針：元の微分と二つの追加作用を成分で展開する。
規約：同じ graded cochain と全ての次数・符号を保持する。
使われ方：D-8 c2 の変形加群の作用と余極限比較射の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R] {K L : Complex R}
  (θ : Cochain K K 1) (ψ : Cochain L L 1)
  (hθ : δ 1 2 θ + θ.comp θ (show (1 : ℤ) + 1 = 2 from rfl) = 0)
  (hψ : δ 1 2 ψ + ψ.comp ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0)

def maurerCartanRebaseCochain {p : ℤ} (f : Cochain K L p) :
    Cochain (maurerCartanPerturbComplex K θ hθ) (maurerCartanPerturbComplex L ψ hψ) p :=
  Cochain.mk (fun i j h => f.v i j h)

def maurerCartanForgetCochain {p : ℤ}
    (f : Cochain (maurerCartanPerturbComplex K θ hθ) (maurerCartanPerturbComplex L ψ hψ) p) :
    Cochain K L p := Cochain.mk (fun i j h => f.v i j h)

lemma maurerCartanHom_δ (p : ℤ) (f : Cochain K L p) :
    maurerCartanForgetCochain θ ψ hθ hψ
      (δ p (p + 1) (maurerCartanRebaseCochain θ ψ hθ hψ f)) =
      δ p (p + 1) f + f.comp ψ rfl +
        (p + 1).negOnePow • θ.comp f (by omega : 1 + p = p + 1) := by
  apply Cochain.ext
  intro i j hij
  obtain rfl : j = i + p + 1 := by omega
  simp only [maurerCartanForgetCochain, Cochain.mk_v]
  rw [δ_v (F := maurerCartanPerturbComplex K θ hθ)
    (G := maurerCartanPerturbComplex L ψ hψ) p (p + 1) rfl _
    i (i + p + 1) (by omega) (i + p) (i + 1) (by omega) rfl]
  simp only [maurerCartanRebaseCochain, Cochain.mk_v]
  rw [maurerCartanPerturbComplex_d, maurerCartanPerturbComplex_d]
  simp only [Cochain.add_v, Cochain.units_smul_v]
  rw [δ_v (F := K) (G := L) p (p + 1) rfl f
      i (i + p + 1) (by omega) (i + p) (i + 1) (by omega) rfl,
    Cochain.comp_v f ψ rfl i (i + p) (i + p + 1) rfl rfl,
    Cochain.comp_v θ f _ i (i + 1) (i + p + 1) rfl (by omega)]
  simp only [comp_add, add_comp, smul_add, Units.smul_def, zsmul_comp]
  abel

end SerrePositivity.DifferentialGraded
