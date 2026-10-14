module
public import SerrePositivity.DifferentialGraded.Complexes.TensorEnriched
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-! # 整数 shift の全次数 dg 関手

Mathlib の cochain shift は Hom 微分を (-1)^s 倍する。
次数 p の Hom には (-1)^(sp) を掛け、chain map を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 整数 shift の Hom chain map。 -/
def shiftHom (s : ℤ) (P Q : Complex A) :
    homComplex A P Q ⟶ homComplex A (P⟦s⟧) (Q⟦s⟧) where
  f p := ModuleCat.ofHom ((s * p).negOnePow • Cochain.shiftLinearMap A P Q p s)
  comm' p q hpq := by
    obtain rfl : q = p + 1 := hpq.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change δ p (p + 1) ((s * p).negOnePow • f.shift s) =
      (s * (p + 1)).negOnePow • (δ p (p + 1) f).shift s
    rw [δ_units_smul, Cochain.δ_shift, smul_smul, ← Int.negOnePow_add]
    congr 2
    ring

/-- 斉次 Hom の shift は射の次数と shift の Koszul 符号を持つ。 -/
lemma shiftHom_apply (s : ℤ) (P Q : Complex A) (p : ℤ) (f : Homogeneous P Q p) :
    (shiftHom s P Q).f p f = (s * p).negOnePow • f.shift s := rfl

/-- shift の全斉次成分。 -/
lemma shiftHom_v (s : ℤ) (P Q : Complex A) (p i j : ℤ) (hij : i + p = j)
    (f : Homogeneous P Q p) :
    ((shiftHom s P Q).f p f).v i j hij =
      (s * p).negOnePow • f.v (i + s) (j + s) (by omega) := by
  rw [shiftHom_apply, Cochain.units_smul_v, Cochain.shift_v']

/-- 閉零次数では Mathlib の通常の chain map shift と一致する。 -/
lemma shiftHom_ofHom (s : ℤ) {P Q : Complex A} (f : P ⟶ Q) :
    (shiftHom s P Q).f 0 (Cochain.ofHom f) = Cochain.ofHom (f⟦s⟧') := by
  apply Cochain.ext₀
  intro i
  rw [shiftHom_v]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, Cochain.ofHom_v]
  rfl

/-- shift の Hom chain map は閉単位を保存する。 -/
lemma shiftHom_identity (s : ℤ) (P : Complex A) :
    identity P ≫ shiftHom s P P = identity (P⟦s⟧) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (identity P ≫ shiftHom s P P)).val =
    (cycleFromUnit _ (identity (P⟦s⟧))).val
  rw [cycleFromUnit_postcomp]
  simp only [identity, cycleFromUnit_unitFromCycle]
  rw [shiftHom_ofHom, CategoryTheory.Functor.map_id]

/-- shift の Hom chain map は豊穣合成を保存する。 -/
lemma shiftHom_comp (s : ℤ) (P Q T : Complex A) :
    enrichedComposition P Q T ≫ shiftHom s P T =
      (shiftHom s P Q ⊗ₘ shiftHom s Q T) ≫ enrichedComposition _ _ _ := by
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change (shiftHom s P T).f n
    ((enrichedComposition P Q T).f n
      (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q n hn (f ⊗ₜ[A] g))) =
    (enrichedComposition _ _ _).f n
      ((shiftHom s P Q ⊗ₘ shiftHom s Q T).f n
        (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q n hn (f ⊗ₜ[A] g)))
  rw [tensorMap_apply, enrichedComposition_apply, enrichedComposition_apply,
    shiftHom_apply, shiftHom_apply, shiftHom_apply]
  simp only [Cochain.shift_units_smul, Cochain.units_smul_comp, Cochain.comp_units_smul, smul_smul]
  apply Cochain.ext
  intro i j hij
  rw [Cochain.units_smul_v, Cochain.units_smul_v, Cochain.shift_v',
    Cochain.comp_v _ _ hn (i + s) (i + p + s) (j + s) (by omega) (by omega),
    Cochain.comp_v _ _ hn i (i + p) j rfl (by omega),
    Cochain.shift_v', Cochain.shift_v']
  have he : (s * n).negOnePow * (p * q).negOnePow =
      (p * q).negOnePow * ((s * p).negOnePow * (s * q).negOnePow) := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add]
    congr 1
    rw [← hn]
    ring
  rw [he, mul_comm (s * p).negOnePow (s * q).negOnePow]

/-- Mathlib の複体 shift を全次数に拡張した主 dg 関手。 -/
def shiftDG (s : ℤ) : DGFunctor A (Complex A) (Complex A) where
  obj P := P⟦s⟧
  map := shiftHom s
  map_id := shiftHom_identity s
  map_comp := shiftHom_comp s
end SerrePositivity.DifferentialGraded
