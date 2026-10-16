module
public import SerrePositivity.DifferentialGraded.Complexes.TensorEnriched
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.UnitScalarEvaluation

/-! # 任意次数のcochainを右tensorする主Hom写像

signed symmetryによる共役で構成する。純tensor上では左因子だけに作用し、追加符号は消える。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 全Homのchain mapは任意整数次数のcocycleをcocycleへ送る。 -/
lemma homComplexMap_closed {P Q R S : Complex A} (F : homComplex A P Q ⟶ homComplex A R S)
    (p : ℤ) (f : Cochain P Q p) (hf : δ p (p + 1) f = 0) :
    δ p (p + 1) (F.f p f) = 0 := by
  have h := ConcreteCategory.congr_hom (F.comm p (p + 1)) f
  change δ p (p + 1) (F.f p f) = F.f (p + 1) (δ p (p + 1) f) at h
  rw [hf, map_zero] at h
  exact h

/-- cochainの各斉次成分は整数単位スカラーを保つ。 -/
lemma cochain_v_units_smul {P Q : Complex A} {p : ℤ} (f : Cochain P Q p)
    (i n : ℤ) (hn : i + p = n) (a : ℤˣ) (x : P.X i) :
    f.v i n hn (a • x) = a • f.v i n hn x := by
  simp only [Units.smul_def, map_zsmul]

/-- 右tensorの全次数Hom写像。 -/
def tensorRightHom (K P Q : Complex A) :
    homComplex A P Q ⟶ homComplex A (P ⊗ K) (Q ⊗ K) :=
  tensorLeftHom K P Q ≫ homPrecompose (signedSwap P K).hom (K ⊗ Q) ≫
    homPostcompose (P ⊗ K) (signedSwap K Q).hom

lemma tensorRightHom_cochain (K P Q : Complex A) (p : ℤ) (f : Cochain P Q p) :
    (tensorRightHom K P Q).f p f =
      ((Cochain.ofHom (signedSwap P K).hom).comp ((tensorLeftHom K P Q).f p f)
        (zero_add p)).comp (Cochain.ofHom (signedSwap K Q).hom) (add_zero p) := rfl

/-- 純tensor上で、右tensorは追加のKoszul符号なしに左因子のcochainを適用する。 -/
lemma tensorRightHom_apply (K P Q : Complex A) (p i j a n : ℤ)
    (ha : i + j = a) (hn : a + p = n) (f : Cochain P Q p) (x : P.X i) (y : K.X j) :
    ((tensorRightHom K P Q).f p f).v a n hn
      (ιTensorObj P K i j a ha (x ⊗ₜ[A] y)) =
    ιTensorObj Q K (i + p) j n (by omega) (f.v i (i + p) rfl x ⊗ₜ[A] y) := by
  rw [tensorRightHom_cochain, cochain_comp_ofHom_apply, cochain_ofHom_comp_apply,
    signedSwap_apply, cochain_v_units_smul,
    tensorLeftHom_apply K P Q p j i a n (by omega) hn f y x,
    chain_units_smul, chain_units_smul, signedSwap_apply]
  simp only [smul_smul, ← Int.negOnePow_add]
  have he : i * j + (p * j + j * (i + p)) = 2 * (j * (i + p)) := by ring
  rw [he, Int.negOnePow_two_mul, one_smul]

end SerrePositivity.DifferentialGraded
