module
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanPerturbation

/-!
概要：標的だけを MC 変形した全次数 Hom の微分を計算する。
方針：元の cochain の成分を保ち、標的微分の追加作用だけを展開する。
規約：始域の複体と全次数を保ち、始域の零変形を別模型として挿入しない。
使われ方：bar の MC 摂動後の終端 HA 成分の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Preadditive HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R] {K L : Complex R}
  (ψ : Cochain L L 1)
  (hψ : δ 1 2 ψ + ψ.comp ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0)

def maurerCartanTargetRebaseCochain {p : ℤ} (f : Cochain K L p) :
    Cochain K (maurerCartanPerturbComplex L ψ hψ) p :=
  Cochain.mk (fun i j hij => f.v i j hij)

def maurerCartanTargetForgetCochain {p : ℤ}
    (f : Cochain K (maurerCartanPerturbComplex L ψ hψ) p) : Cochain K L p :=
  Cochain.mk (fun i j hij => f.v i j hij)

lemma maurerCartanTargetHom_δ (p : ℤ) (f : Cochain K L p) :
    maurerCartanTargetForgetCochain ψ hψ
      (δ p (p + 1) (maurerCartanTargetRebaseCochain ψ hψ f)) =
      δ p (p + 1) f + f.comp ψ rfl := by
  apply Cochain.ext
  intro i j hij
  obtain rfl : j = i + p + 1 := by omega
  simp only [maurerCartanTargetForgetCochain, Cochain.mk_v]
  rw [δ_v (F := K) (G := maurerCartanPerturbComplex L ψ hψ) p (p + 1) rfl _
    i (i + p + 1) (by omega) (i + p) (i + 1) (by omega) rfl]
  simp only [maurerCartanTargetRebaseCochain, Cochain.mk_v]
  rw [maurerCartanPerturbComplex_d]
  simp only [Cochain.add_v]
  rw [δ_v (F := K) (G := L) p (p + 1) rfl f
    i (i + p + 1) (by omega) (i + p) (i + 1) (by omega) rfl,
    Cochain.comp_v f ψ rfl i (i + p) (i + p + 1) rfl rfl]
  simp only [comp_add]
  abel

end SerrePositivity.DifferentialGraded
