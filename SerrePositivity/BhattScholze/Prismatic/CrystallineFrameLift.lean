module

public import SerrePositivity.BhattScholze.Prismatic.CrystallineNilpotentComplete
public import SerrePositivity.BhattScholze.Prismatic.CrystallineResidue
public import SerrePositivity.BhattScholze.Prismatic.CrystallineResidueAlgebra
public import SerrePositivity.BhattScholze.Prismatic.PDCechNerve
import all SerrePositivity.BhattScholze.Prismatic.CompletedPDEnvelope
import all SerrePositivity.BhattScholze.Prismatic.PDCechNerve

/-!
# 分冪枠から結晶厚化への持ち上げ

## 概要
枠の各変数を厚化へ持ち上げ、分冪包の普遍性で厚化の台環への射を作る。

## 方針
商写像の全射性で変数像を選ぶ。核が分冪イデアルに入ることを剰余の正方形で示す。

## 規約
標的は p 冪零なので p 完備。平坦性や正則性は仮定しない。

## 使われ方
Berthelot III.4、Stacks 07HP。分冪 Čech の塔の pro 弱終性。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable {p : ℕ} {k : Type u} [CommRing k] {J : Ideal k} {γ : DividedPowers J}
variable {R : Type u} [CommRing R] [Algebra (k ⧸ J) R]
variable [Algebra k R] [IsScalarTower k (k ⧸ J) R] {κ : Cardinal.{u}}
variable (X : CrysOver p γ R κ) {S : Type u} (s : S → R)

/-- 係数構造の塔のもとで、剰余構造射を代数射として読む。 -/
def crysResidueSectionAlgHom : R →ₐ[k] X.B ⧸ X.JB where
  __ := X.sec
  commutes' a := by
    have ha : algebraMap k R a = algebraMap (k ⧸ J) R (Ideal.Quotient.mk J a) :=
      IsScalarTower.algebraMap_apply k (k ⧸ J) R a
    rw [ha]
    exact DFunLike.congr_fun X.sec_comp a

/-- 枠の各変数の剰余構造射の像を厚化に持ち上げる。 -/
def crysFrameLiftVariables (n : ℕ) (x : S × Fin (n + 1)) : X.B :=
  (Ideal.Quotient.mk_surjective (X.sec (s x.1))).choose

omit [Algebra k R] [IsScalarTower k (k ⧸ J) R] in
/-- 選んだ変数像は元の剰余構造射に写る。 -/
theorem crysFrameLiftVariables_mk (n : ℕ) (x : S × Fin (n + 1)) :
    Ideal.Quotient.mk X.JB (crysFrameLiftVariables X s n x) = X.sec (s x.1) :=
  (Ideal.Quotient.mk_surjective (X.sec (s x.1))).choose_spec

/-- 選んだ変数像による多項式枠の代数射。 -/
def crysFrameLiftPolynomial (n : ℕ) : pdFrame k S n →ₐ[k] X.B :=
  MvPolynomial.aeval (crysFrameLiftVariables X s n)

/-- 多項式枠の射は剰余で元の評価と可換。 -/
theorem crysFrameLiftPolynomial_residue (n : ℕ) :
    (Ideal.Quotient.mkₐ k X.JB).comp (crysFrameLiftPolynomial X s n) =
      (crysResidueSectionAlgHom X).comp (pdFrameEval (k := k) s n) := by
  apply MvPolynomial.algHom_ext
  intro x
  change Ideal.Quotient.mk X.JB (MvPolynomial.aeval (crysFrameLiftVariables X s n)
    (MvPolynomial.X x)) = X.sec (pdFrameEval (k := k) s n (MvPolynomial.X x))
  rw [MvPolynomial.aeval_X, pdFrameEval_X]
  exact crysFrameLiftVariables_mk X s n x

/-- 枠の評価の核は、持ち上げの像で厚化の分冪イデアルに入る。 -/
theorem crysFrameLiftPolynomial_kernel (n : ℕ) :
    (RingHom.ker (pdFrameEval (k := k) s n)).map
      (crysFrameLiftPolynomial X s n).toRingHom ≤ X.JB := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro b hb
  change crysFrameLiftPolynomial X s n b ∈ X.JB
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h := DFunLike.congr_fun (crysFrameLiftPolynomial_residue X s n) b
  change Ideal.Quotient.mk X.JB (crysFrameLiftPolynomial X s n b) =
    X.sec (pdFrameEval (k := k) s n b) at h
  rw [RingHom.mem_ker.mp hb, map_zero] at h
  exact h

variable (hp : (p : k) ∈ J)
local notation "hJ" => crysResidue_kernel_of_tower (J := J) R
local notation "D" n => PDCechNerve.term p γ hp hJ s n

/-- 完備分冪包の普遍性による、枠から結晶厚化への持ち上げ。 -/
def crystallineFrameLift (n : ℕ) : (D n).carrier →ₐ[k] X.B :=
  (D n).isEnvelope.liftHom (ε := X.δ) X.isAdicComplete (crysFrameLiftPolynomial X s n)
    (crysFrameLiftPolynomial_kernel X s n) X.base_dp

/-- 持ち上げは分冪射。 -/
theorem crystallineFrameLift_dp (n : ℕ) :
    (D n).dividedPowers.IsDPMorphism X.δ (crystallineFrameLift X s hp n).toRingHom :=
  (D n).isEnvelope.liftHom_isDPMorphism ..

/-- 持ち上げは多項式枠の上で指定した評価に一致する。 -/
@[simp] theorem crystallineFrameLift_unit (n : ℕ) (f : pdFrame k S n) :
    crystallineFrameLift X s hp n ((D n).unit f) = crysFrameLiftPolynomial X s n f :=
  DFunLike.congr_fun ((D n).isEnvelope.liftHom_comp ..) f

/-- 持ち上げは、分冪包の増強と厚化の剰余構造射との正方形を保つ。 -/
theorem crystallineFrameLift_residue (n : ℕ) :
    (Ideal.Quotient.mk X.JB).comp (crystallineFrameLift X s hp n).toRingHom =
      X.sec.comp (PDCechNerve.augmentation p γ hp hJ s n).toRingHom := by
  let f := (Ideal.Quotient.mkₐ k X.JB).comp (crystallineFrameLift X s hp n)
  let g := (crysResidueSectionAlgHom X).comp (PDCechNerve.augmentation p γ hp hJ s n)
  have ht : IsAdicComplete (Ideal.span {(p : X.B ⧸ X.JB)}) (X.B ⧸ X.JB) := by
    apply isAdicComplete_of_natCast_zero
    change Ideal.Quotient.mk X.JB (p : X.B) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (X.prime_mem hp)
  have h : f = g := by
    apply (D n).isEnvelope.hom_ext ht
      (isDPMorphismToBot (D n).dividedPowers f.toRingHom (fun a ha => by
        change Ideal.Quotient.mk X.JB (crystallineFrameLift X s hp n a) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          ((crystallineFrameLift_dp X s hp n).ideal_comp (Ideal.mem_map_of_mem _ ha))))
      (isDPMorphismToBot (D n).dividedPowers g.toRingHom (fun a ha => by
        change X.sec (PDCechNerve.augmentation p γ hp hJ s n a) = 0
        have hz : PDCechNerve.augmentation p γ hp hJ s n a = 0 :=
          RingHom.mem_ker.mp ((PDCechNerve.augmentation_ker p γ hp hJ s n).symm ▸ ha)
        rw [hz, map_zero]))
    apply AlgHom.ext
    intro a
    change Ideal.Quotient.mk X.JB
      (crystallineFrameLift X s hp n ((D n).unit a)) =
        X.sec (PDCechNerve.augmentation p γ hp hJ s n ((D n).unit a))
    rw [crystallineFrameLift_unit, PDCechNerve.augmentation_unit]
    exact DFunLike.congr_fun (crysFrameLiftPolynomial_residue X s n) a
  exact congrArg AlgHom.toRingHom h

end SerrePositivity.BhattScholze.Prismatic
