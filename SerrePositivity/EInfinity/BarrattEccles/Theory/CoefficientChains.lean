module

public import SerrePositivity.EInfinity.BarrattEccles.Generators
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCochainDegrees
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules

/-!
# Barratt–Eccles の正規化鎖の係数写像

## 概要
Berger–Fresse §1.1.2 の正規化鎖に環準同型に沿う係数写像を与える。

## 方針
同じ非退化単体で添字付けた基底から写像を作り、交代面の公式で微分と比較する。

## 規約
任意の可換環準同型を扱い、退化した生成元は零に送る。

## 使われ方
Barratt–Eccles オペラッドと代数の係数変更。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits HomologicalComplex DifferentialGraded
open scoped Simplicial

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- 非退化基底を保つ自然数次数ごとの半線形写像。 -/
def normalizedCoefficientComponent (n q : ℕ) :
    (normalizedChains S n).X q ⟶
      (ModuleCat.restrictScalars f).obj ((normalizedChains T n).X q) :=
  let M := (ModuleCat.restrictScalars f).obj ((normalizedChains T n).X q)
  let v : ULift.{u} ((simplicial n).nonDegenerate q) → M := normalizedBasis T n q
  ModuleCat.ofHom (Y := M) ((normalizedBasis S n q).constr S v)

/-- 退化単体も含めて、係数写像は同じ単体の生成元を与える。 -/
lemma normalizedCoefficientComponent_generator (n q : ℕ) (x : (simplicial n) _⦋q⦌) :
    normalizedCoefficientComponent f n q (normalizedGenerator S n q x) =
      normalizedGenerator T n q x := by
  by_cases h : x ∈ (simplicial n).nonDegenerate q
  · let y : (simplicial n).nonDegenerate q := ⟨x, h⟩
    rw [← normalizedBasis_apply S n q y, ← normalizedBasis_apply T n q y]
    let M := (ModuleCat.restrictScalars f).obj ((normalizedChains T n).X q)
    let v : ULift.{u} ((simplicial n).nonDegenerate q) → M := normalizedBasis T n q
    exact Module.Basis.constr_basis (normalizedBasis S n q) S v (ULift.up y)
  · have hd : x ∈ (simplicial n).degenerate q := Classical.not_not.mp (fun hx => h hx)
    rw [normalizedGenerator_degenerate S n q x hd, map_zero,
      normalizedGenerator_degenerate T n q x hd]

/-- 正規化鎖の係数写像は交代面の微分と可換。 -/
def normalizedCoefficientMap (n : ℕ) :
    normalizedChains S n ⟶
      ((ModuleCat.restrictScalars f).mapHomologicalComplex (.down ℕ)).obj
        (normalizedChains T n) where
  f := normalizedCoefficientComponent f n
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    apply normalizedGenerator_hom_ext S
    intro x
    change (normalizedChains T n).d (j + 1) j
        (normalizedCoefficientComponent f n (j + 1) (normalizedGenerator S n (j + 1) x)) =
      normalizedCoefficientComponent f n j
        ((normalizedChains S n).d (j + 1) j (normalizedGenerator S n (j + 1) x))
    rw [normalizedCoefficientComponent_generator, normalizedGenerator_d, normalizedGenerator_d]
    simp only [map_sum, map_zsmul, normalizedCoefficientComponent_generator]

/-- 係数写像の整数余鎖次数への延長。 -/
def coefficientComplexComponent (n : ℕ) (i : ℤ) :
    (complex S n).X i ⟶ (ModuleCat.restrictScalars f).obj ((complex T n).X i) :=
  if hi : i ≤ 0 then
    (complexXIsoNonpos S n i hi).hom ≫ normalizedCoefficientComponent f n (-i).toNat ≫
      (ModuleCat.restrictScalars f).map (complexXIsoNonpos T n i hi).inv
  else 0

/-- Barratt–Eccles の arity 複体の係数写像。 -/
def coefficientComplexMap (n : ℕ) :
    complex S n ⟶ (ScalarExtension.restriction f).obj (complex T n) where
  f := coefficientComplexComponent f n
  comm' i j _ := by
    symm
    let R := ModuleCat.restrictScalars f
    change (complex S n).d i j ≫ coefficientComplexComponent f n j =
      coefficientComplexComponent f n i ≫ R.map ((complex T n).d i j)
    by_cases hi : i ≤ 0
    · by_cases hj : j ≤ 0
      · simp only [coefficientComplexComponent, dite_eq_left hi, dite_eq_left hj, Category.assoc]
        have hs := complexXIsoNonpos_hom_d S n i j hi hj
        have ht := complexXIsoNonpos_hom_d T n i j hi hj
        have ht' : (complexXIsoNonpos T n i hi).inv ≫ (complex T n).d i j =
            (normalizedChains T n).d (-i).toNat (-j).toNat ≫
              (complexXIsoNonpos T n j hj).inv := by
          apply (cancel_mono (complexXIsoNonpos T n j hj).hom).mp
          simp only [Category.assoc, ht, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
        have hc := ((normalizedCoefficientMap f n).comm (-i).toNat (-j).toNat).symm
        change (normalizedChains S n).d (-i).toNat (-j).toNat ≫
            normalizedCoefficientComponent f n (-j).toNat =
          normalizedCoefficientComponent f n (-i).toNat ≫
            R.map ((normalizedChains T n).d (-i).toNat (-j).toNat) at hc
        rw [reassoc_of% hs, reassoc_of% hc]
        change _ ≫ _ ≫ R.map _ ≫ R.map _ = _ ≫ _ ≫ R.map _ ≫ R.map _
        simp only [← R.map_comp, ht']
      · exact (R.map_isZero (complex_isZero_positive T n j (lt_of_not_ge hj))).eq_of_tgt _ _
    · exact (complex_isZero_positive S n i (lt_of_not_ge hi)).eq_of_src _ _

/-- 次数 −q における係数写像は、正規化鎖の係数写像から計算される。 -/
lemma coefficientComplexMap_f_neg (n q : ℕ) :
    (coefficientComplexMap f n).f (-(q : ℤ)) =
      (complexXIso S n q).hom ≫ normalizedCoefficientComponent f n q ≫
        (ModuleCat.restrictScalars f).map (complexXIso T n q).inv := by
  change coefficientComplexComponent f n (-(q : ℤ)) = _
  unfold coefficientComplexComponent
  rw [dite_eq_left (by omega : -(q : ℤ) ≤ 0)]
  cases q <;> rfl

/-- 係数写像の負次数での値を整数余鎖の生成元で読む。 -/
lemma coefficientComplexMap_generator (n q : ℕ) (x : (simplicial n) _⦋q⦌) :
    (coefficientComplexMap f n).f (-(q : ℤ))
      ((complexXIso S n q).inv (normalizedGenerator S n q x)) =
      (complexXIso T n q).inv (normalizedGenerator T n q x) := by
  rw [coefficientComplexMap_f_neg]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  change (complexXIso T n q).inv
    (normalizedCoefficientComponent f n q (normalizedGenerator S n q x)) = _
  rw [normalizedCoefficientComponent_generator]

end SerrePositivity.EInfinity.BarrattEccles
