module

public import SerrePositivity.AlgebraicGeometry.SchemeAffineClosedBaseChangeSections
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
概要：実際の I 進閉厚化を pullback として作り、指数の間の遷移を構成する。
方針：商環の canonical な射と pullback の普遍性を使う。
規約：スキームの射と、Spec の商射の向きを明示する。
使われ方：形式関数の互換族を、実際の閉厚化の間の引き戻しで述べる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}}
variable (iX : X ⟶ Spec (CommRingCat.of R))

/-- 実際の Iⁿ による閉厚化。 -/
abbrev schemeAdicBaseChange (n : ℕ) : Scheme.{u} :=
  pullback iX (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))))

/-- 閉厚化から元のスキームへの射。 -/
abbrev schemeAdicBaseChangeProjection (n : ℕ) : schemeAdicBaseChange I iX n ⟶ X :=
  pullback.fst _ _

/-- 閉厚化の商環上の構造射。 -/
abbrev schemeAdicBaseChangeStructure (n : ℕ) :
    schemeAdicBaseChange I iX n ⟶ Spec (CommRingCat.of (R ⧸ I ^ n)) :=
  pullback.snd _ _

/-- 定義した閉厚化は、実際に元の構造射の底変換。 -/
theorem schemeAdicBaseChange_isPullback (n : ℕ) :
    IsPullback (schemeAdicBaseChangeProjection I iX n) (schemeAdicBaseChangeStructure I iX n)
      iX (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))) :=
  IsPullback.of_hasPullback _ _

/-- 小さい指数の閉厚化から大きい指数の閉厚化への canonical な射。 -/
def schemeAdicBaseChangeTransition (i j : ℕ) (h : j ≤ i) :
    schemeAdicBaseChange I iX j ⟶ schemeAdicBaseChange I iX i :=
  pullback.lift (schemeAdicBaseChangeProjection I iX j)
    (schemeAdicBaseChangeStructure I iX j ≫ Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (show I ^ i ≤ I ^ j from Ideal.pow_le_pow_right h)))) (by
      rw [pullback.condition]
      simp only [Category.assoc, ← Spec.map_comp]
      congr 2)

/-- 閉厚化の遷移は、元のスキームへの射と可換。 -/
theorem schemeAdicBaseChangeTransition_projection (i j : ℕ) (h : j ≤ i) :
    schemeAdicBaseChangeTransition I iX i j h ≫ schemeAdicBaseChangeProjection I iX i =
      schemeAdicBaseChangeProjection I iX j := by
  simp only [schemeAdicBaseChangeTransition, schemeAdicBaseChangeProjection, pullback.lift_fst]

/-- 閉厚化の遷移は、基底の商環の射とも可換。 -/
theorem schemeAdicBaseChangeTransition_structure (i j : ℕ) (h : j ≤ i) :
    schemeAdicBaseChangeTransition I iX i j h ≫ schemeAdicBaseChangeStructure I iX i =
      schemeAdicBaseChangeStructure I iX j ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (show I ^ i ≤ I ^ j from Ideal.pow_le_pow_right h))) := by
  simp only [schemeAdicBaseChangeTransition, schemeAdicBaseChangeStructure, pullback.lift_snd]

/-- 同じ指数の閉厚化の遷移は恒等射。 -/
theorem schemeAdicBaseChangeTransition_self (i : ℕ) :
    schemeAdicBaseChangeTransition I iX i i le_rfl = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [schemeAdicBaseChangeTransition_projection, Category.id_comp]
  · simp only [schemeAdicBaseChangeTransition_structure, Ideal.Quotient.factor_eq,
      CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, Category.id_comp]

/-- 閉厚化の遷移を二度合成すると、直接の遷移になる。 -/
theorem schemeAdicBaseChangeTransition_comp (i j k : ℕ) (hji : j ≤ i) (hkj : k ≤ j) :
    schemeAdicBaseChangeTransition I iX j k hkj ≫ schemeAdicBaseChangeTransition I iX i j hji =
      schemeAdicBaseChangeTransition I iX i k (hkj.trans hji) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, schemeAdicBaseChangeTransition_projection]
  · simp only [Category.assoc, schemeAdicBaseChangeTransition_structure, ← Spec.map_comp]
    rw [← Category.assoc, schemeAdicBaseChangeTransition_structure I iX j k hkj,
      Category.assoc, ← Spec.map_comp]
    have hc : CommRingCat.ofHom (Ideal.Quotient.factor
        (show I ^ i ≤ I ^ j from Ideal.pow_le_pow_right hji)) ≫
        CommRingCat.ofHom (Ideal.Quotient.factor
          (show I ^ j ≤ I ^ k from Ideal.pow_le_pow_right hkj)) =
        CommRingCat.ofHom (Ideal.Quotient.factor
          (show I ^ i ≤ I ^ k from Ideal.pow_le_pow_right (hkj.trans hji))) := by
      apply CommRingCat.hom_ext
      exact Ideal.Quotient.factor_comp
        (show I ^ i ≤ I ^ j from Ideal.pow_le_pow_right hji)
        (show I ^ j ≤ I ^ k from Ideal.pow_le_pow_right hkj)
    exact congrArg (fun f : CommRingCat.of (R ⧸ I ^ i) ⟶ CommRingCat.of (R ⧸ I ^ k) ↦
      schemeAdicBaseChangeStructure I iX k ≫ Spec.map f) hc

end SerrePositivity.AlgebraicGeometry
