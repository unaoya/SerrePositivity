module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.MonicPowerFamilyCover
public import SerrePositivity.BhattScholze.Perfectoidization.PerfectCoefficientTensor

/-! # B4-6：通常のモニック冪根添加環の普遍性

指定した冪根を持つ任意の通常環への、係数と根を保つ一意な写像を構成する。
完備性・perfectoid性は要求しない。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] polynomialExpandAlgebra monicPowerFamilyExpandModule
variable (n : ℕ) (σ : Type u) (R : Type v) [CommRing R]

/-- expand作用の型名と台多項式環の標準ULift同型。 -/
def monicPowerFamilyTargetEquiv : PolynomialExpandTarget n σ R ≃+* MvPolynomial σ R :=
  ULift.ringEquiv

/-- テンソル積の右因子から根添加環への標準射。 -/
def monicPowerFamilyCoverRightMap (c : σ → R) :
    PolynomialExpandTarget n σ R →+* MonicPowerFamilyCover n σ R c := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  exact (Algebra.TensorProduct.includeRight : PolynomialExpandTarget n σ R →ₐ[MvPolynomial σ R]
    R ⊗[MvPolynomial σ R] PolynomialExpandTarget n σ R).toRingHom

/-- 右因子の係数は、根添加環の標準係数射の像と一致する。 -/
theorem monicPowerFamilyCoverRightMap_C (c : σ → R) (r : R) :
    monicPowerFamilyCoverRightMap n σ R c (ULift.up (MvPolynomial.C r)) =
      algebraMap R (MonicPowerFamilyCover n σ R c) r := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  let P := MvPolynomial σ R
  let Q := R ⊗[P] PolynomialExpandTarget n σ R
  have hb : algebraMap P (PolynomialExpandTarget n σ R) (MvPolynomial.C r) =
      ULift.up (MvPolynomial.C r) := by
    change ULift.up (MvPolynomial.expand n (MvPolynomial.C r)) = _
    rw [MvPolynomial.expand_C]
  have ha : algebraMap P R (MvPolynomial.C r) = r := MvPolynomial.aeval_C c r
  have hright := (Algebra.TensorProduct.includeRight :
    PolynomialExpandTarget n σ R →ₐ[P] Q).commutes (MvPolynomial.C r)
  have hleft := (Algebra.TensorProduct.includeLeft : R →ₐ[P] Q).commutes (MvPolynomial.C r)
  rw [hb] at hright
  rw [ha] at hleft
  exact hright.trans hleft.symm

/-- 右因子の変数の像は、指定した根。 -/
@[simp] theorem monicPowerFamilyCoverRightMap_X (c : σ → R) (s : σ) :
    monicPowerFamilyCoverRightMap n σ R c (ULift.up (MvPolynomial.X s)) =
      monicPowerFamilyRoot n σ R c s := rfl

/-- 根添加環からの環射は、係数と指定根の像で決まる。 -/
theorem monicPowerFamilyCoverHom_ext (c : σ → R) {U : Type w} [CommRing U]
    (L M : MonicPowerFamilyCover n σ R c →+* U)
    (hR : L.comp (algebraMap R (MonicPowerFamilyCover n σ R c)) =
      M.comp (algebraMap R (MonicPowerFamilyCover n σ R c)))
    (hroot : ∀ s, L (monicPowerFamilyRoot n σ R c s) = M (monicPowerFamilyRoot n σ R c s)) :
    L = M := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  apply Algebra.TensorProduct.ringHom_ext
  · exact hR
  · let i := monicPowerFamilyCoverRightMap n σ R c
    let e := monicPowerFamilyTargetEquiv n σ R
    have he : (L.comp i).comp e.symm.toRingHom = (M.comp i).comp e.symm.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        change L (i (ULift.up (MvPolynomial.C r))) = M (i (ULift.up (MvPolynomial.C r)))
        rw [monicPowerFamilyCoverRightMap_C]
        exact RingHom.congr_fun hR r
      · intro s
        exact hroot s
    apply RingHom.ext
    intro x
    have hx := RingHom.congr_fun he (e x)
    change L (i (e.symm (e x))) = M (i (e.symm (e x))) at hx
    rw [e.symm_apply_apply] at hx
    exact hx

/-- 指定根を持つ終域への環射を、既存テンソル積の普遍射から構成する。 -/
def monicPowerFamilyCoverMap (c : σ → R) {U : Type w} [CommRing U]
    (f : R →+* U) (b : σ → U) (hb : ∀ s, b s ^ n = f (c s)) :
    MonicPowerFamilyCover n σ R c →+* U := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  let e := monicPowerFamilyTargetEquiv n σ R
  let g := (MvPolynomial.eval₂Hom f b).comp e.toRingHom
  have he : f.comp (algebraMap (MvPolynomial σ R) R) =
      g.comp (algebraMap (MvPolynomial σ R) (PolynomialExpandTarget n σ R)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change f (MvPolynomial.aeval c (MvPolynomial.C r)) =
        MvPolynomial.eval₂Hom f b (MvPolynomial.expand n (MvPolynomial.C r))
      rw [MvPolynomial.aeval_C, MvPolynomial.expand_C, MvPolynomial.eval₂Hom_C]
      rfl
    · intro s
      change f (MvPolynomial.aeval c (MvPolynomial.X s)) =
        MvPolynomial.eval₂Hom f b (MvPolynomial.expand n (MvPolynomial.X s))
      rw [MvPolynomial.aeval_X, MvPolynomial.expand_X, map_pow, MvPolynomial.eval₂Hom_X']
      exact (hb s).symm
  exact coefficientTensorLift f g (RingHom.congr_fun he)

/-- 普遍射は係数射を保つ。 -/
theorem monicPowerFamilyCoverMap_comp (c : σ → R) {U : Type w} [CommRing U]
    (f : R →+* U) (b : σ → U) (hb : ∀ s, b s ^ n = f (c s)) :
    (monicPowerFamilyCoverMap n σ R c f b hb).comp
      (algebraMap R (MonicPowerFamilyCover n σ R c)) = f := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  apply RingHom.ext
  intro r
  change monicPowerFamilyCoverMap n σ R c f b hb
    (r ⊗ₜ[MvPolynomial σ R] (1 : PolynomialExpandTarget n σ R)) = f r
  change f r * ((MvPolynomial.eval₂Hom f b).comp
    (monicPowerFamilyTargetEquiv n σ R).toRingHom) 1 = f r
  rw [map_one, mul_one]

/-- 普遍射は指定根を保つ。 -/
@[simp] theorem monicPowerFamilyCoverMap_root (c : σ → R) {U : Type w} [CommRing U]
    (f : R →+* U) (b : σ → U) (hb : ∀ s, b s ^ n = f (c s)) (s : σ) :
    monicPowerFamilyCoverMap n σ R c f b hb (monicPowerFamilyRoot n σ R c s) = b s := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  change monicPowerFamilyCoverMap n σ R c f b hb
    (TensorProduct.tmul (R := MvPolynomial σ R) (M := R)
      (N := PolynomialExpandTarget n σ R) 1 (ULift.up (MvPolynomial.X s))) = b s
  change f 1 * MvPolynomial.eval₂Hom f b (MvPolynomial.X s) = b s
  rw [map_one, one_mul, MvPolynomial.eval₂Hom_X']

/-- 任意の通常環の指定n乗根への、係数と根を保つ環射は一意に存在する。 -/
theorem existsUnique_monicPowerFamilyCoverMap (c : σ → R) {U : Type w} [CommRing U]
    (f : R →+* U) (b : σ → U) (hb : ∀ s, b s ^ n = f (c s)) :
    ∃! L : MonicPowerFamilyCover n σ R c →+* U,
      L.comp (algebraMap R (MonicPowerFamilyCover n σ R c)) = f ∧
        ∀ s, L (monicPowerFamilyRoot n σ R c s) = b s := by
  refine ⟨monicPowerFamilyCoverMap n σ R c f b hb,
    ⟨monicPowerFamilyCoverMap_comp n σ R c f b hb,
      monicPowerFamilyCoverMap_root n σ R c f b hb⟩, ?_⟩
  intro L hL
  exact monicPowerFamilyCoverHom_ext n σ R c L _
    (hL.1.trans (monicPowerFamilyCoverMap_comp n σ R c f b hb).symm)
    (fun s ↦ (hL.2 s).trans (monicPowerFamilyCoverMap_root n σ R c f b hb s).symm)

end SerrePositivity.BhattScholze
