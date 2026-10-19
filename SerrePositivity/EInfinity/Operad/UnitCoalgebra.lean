module

public import SerrePositivity.EInfinity.Operad.CoalgebraInterval
public import SerrePositivity.EInfinity.Operad.CoInsertionUnit

/-!
# Augmentation に付随する単位余代数

概要：Berger–Fresse §3.1 の単位対象上の余演算を実際の P 余代数へ束ねる。
方針：単位冪の縮約の後で augmentation の単位・等変性・部分合成の保存を使う。
規約：任意の augmentation を扱い、Hopf 対角は構成に要求しない。
使われ方：余代数区間の端点・収縮を余代数射として公開する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

private lemma unitCoefficient_comp {K : Type u} [Category.{v} K] [MonoidalCategory K]
    [SymmetricCategory K] {C D : K} (f : C ⟶ 𝟙_ K) (g : D ⟶ 𝟙_ K) :
    ((β_ C D).hom ▷ (𝟙_ K)) ≫ (α_ D C (𝟙_ K)).hom ≫
      (D ◁ ((f ▷ (𝟙_ K)) ≫ (λ_ (𝟙_ K)).hom)) ≫
      (g ▷ (𝟙_ K)) ≫ (λ_ (𝟙_ K)).hom =
    ((f ⊗ₘ g) ▷ (𝟙_ K)) ≫ ((λ_ (𝟙_ K)).hom ▷ (𝟙_ K)) ≫
      (λ_ (𝟙_ K)).hom := by
  calc
    _ = ((β_ C D).hom ▷ (𝟙_ K)) ≫ ((g ⊗ₘ f) ▷ (𝟙_ K)) ≫
        (α_ (𝟙_ K) (𝟙_ K) (𝟙_ K)).hom ≫
        ((𝟙_ K) ◁ (λ_ (𝟙_ K)).hom) ≫ (λ_ (𝟙_ K)).hom := by
      rw [tensorHom_def' g f]
      simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
      monoidal
    _ = _ := by
      rw [← comp_whiskerRight_assoc, ← BraidedCategory.braiding_naturality,
        comp_whiskerRight]
      rw [braiding_tensorUnit_left]
      simp only [comp_whiskerRight, Category.assoc]
      monoidal

variable {A : Type u} [CommRing A] {P : Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- 概要：単位余演算の出力の縮約は augmentation の評価となる（BF §3.1）。
方針：単位冪の縮約同型の逆射を相殺する。
規約：出力数零を含む。
使われ方：単位余代数の公理を単位対象への射で比較する。 -/
@[reassoc]
lemma unitCoaction_contract (ε : P ⟶ commutativeOperad A) (n : ℕ) :
    unitCoaction ε n ≫ (tensorUnitPowerIso (Complex A) n).hom =
      (ε.map.app (FiniteBijection.of n) ▷ (𝟙_ (Complex A))) ≫
        (λ_ (𝟙_ (Complex A))).hom := by
  simp only [unitCoaction, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：単位余演算は対称群作用を保つ（BF §3.1）。
方針：単位冪の置換が恒等射であることと augmentation の自然性を使う。
規約：全ての置換を扱う。
使われ方：単位余代数の等変性の公理となる。 -/
lemma unitCoaction_equivariance (ε : P ⟶ commutativeOperad A) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    (P.sequence.map (FiniteBijection.permutation n σ) ▷ (𝟙_ (Complex A))) ≫
      unitCoaction ε n = unitCoaction ε n ≫
        (permutationAction (𝟙_ (Complex A)) n σ).asIso.hom := by
  rw [tensorUnitPower_permutation, Category.comp_id]
  have he : P.sequence.map (FiniteBijection.permutation n σ) ≫
      ε.map.app (FiniteBijection.of n) = ε.map.app (FiniteBijection.of n) := by
    have h := ε.map.naturality (FiniteBijection.permutation n σ)
    change _ = _ ≫ 𝟙 (𝟙_ (Complex A)) at h
    simpa only [Category.comp_id] using h
  simp only [unitCoaction]
  rw [← comp_whiskerRight_assoc, he]

/-- 概要：単位演算は単位対象の恒等余演算となる（BF §3.1）。
方針：一次の単位冪の比較と augmentation の単位保存を使う。
規約：左単位子を明示する。
使われ方：単位余代数の単位公理となる。 -/
lemma unitCoaction_unit (ε : P ⟶ commutativeOperad A) :
    (P.unit ▷ (𝟙_ (Complex A))) ≫ unitCoaction ε 1 ≫
      (oneIso (𝟙_ (Complex A))).hom = (λ_ (𝟙_ (Complex A))).hom := by
  rw [← tensorUnitPowerIso_one, unitCoaction_contract]
  have he : P.unit ≫ ε.map.app (FiniteBijection.of 1) = 𝟙 _ := ε.unit
  rw [← comp_whiskerRight_assoc, he]
  simp only [id_whiskerRight, Category.id_comp]

/-- 概要：単位余演算は全位置で部分合成を保つ（BF §3.1）。
方針：出力の縮約で比較し、augmentation の合成保存と単位係数の交換を使う。
規約：出力数零の内側演算を含む。
使われ方：単位対象を実際の P 余代数へ束ねる。 -/
lemma unitCoaction_partialComposition (ε : P ⟶ commutativeOperad A) (m n : ℕ) (i : Fin (m + 1)) :
    (P.comp m n i ▷ (𝟙_ (Complex A))) ≫ unitCoaction ε (m + n) =
    ((β_ (P.arity (m + 1)) (P.arity n)).hom ▷ (𝟙_ (Complex A))) ≫
      (α_ (P.arity n) (P.arity (m + 1)) (𝟙_ (Complex A))).hom ≫
      (P.arity n ◁ unitCoaction ε (m + 1)) ≫
      tensorCoInsertionAction (𝟙_ (Complex A)) (P.arity n) m n i (unitCoaction ε n) := by
  apply (cancel_mono (tensorUnitPowerIso (Complex A) (m + n)).hom).1
  simp only [Category.assoc]
  rw [unitCoaction_contract, tensorCoInsertionAction_unit]
  rw [← whiskerLeft_comp_assoc, unitCoaction_contract]
  rw [unitCoaction_contract]
  have he : P.comp m n i ≫ ε.map.app (FiniteBijection.of (m + n)) =
      (ε.map.app (FiniteBijection.of (m + 1)) ⊗ₘ ε.map.app (FiniteBijection.of n)) ≫
        (λ_ (𝟙_ (Complex A))).hom := ε.comp m n i
  rw [← comp_whiskerRight_assoc, he, comp_whiskerRight]
  exact (unitCoefficient_comp (ε.map.app (FiniteBijection.of (m + 1)))
    (ε.map.app (FiniteBijection.of n))).symm

/-- 概要：augmentation に付随するテンソル単位上の P 余代数（BF §3.1）。
方針：明示的な余演算と三つの保存則を束ねる。
規約：Hopf 対角やモデル構造を仮定しない。
使われ方：余代数区間の端点・収縮の始域と終域となる。 -/
def unitCoalgebra (ε : P ⟶ commutativeOperad A) : P.Coalgebra where
  carrier := 𝟙_ (Complex A)
  coaction := unitCoaction ε
  equivariance := unitCoaction_equivariance ε
  unit_coaction := unitCoaction_unit ε
  comp_coaction := unitCoaction_partialComposition ε

end SerrePositivity.EInfinity.Operad
