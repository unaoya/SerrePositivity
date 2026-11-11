module

public import SerrePositivity.EInfinity.Operad.Commutative
public import SerrePositivity.EInfinity.Operad.CompositionAdjacentFactor
public import SerrePositivity.EInfinity.Operad.TensorUnitFamily
public import SerrePositivity.EInfinity.Operad.TensorSubstitutionRightUnit

/-!
# 可換オペラッドの反復合成

## 概要
HA 3.2.4.7 の二色係数の増大の値となる可換オペラッドの反復合成を計算する。

## 方針
全ての arity がテンソル単位であることを使い、最後の代入と残りの縮約を単位族の縮約へまとめる。

## 規約
内側 arity は零も含む任意の自然数。

## 使われ方
零入力への係数射影と増大の可換性の終域の計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open scoped BigOperators
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
variable (A : Type u) [CommRing A]

/-- 可換オペラッドの一段の代入は、テンソル単位の右単位子である。 -/
lemma commutativeInsertion_eq (n k l : ℕ) :
    (commutativeOperad A).composeFirstInputInsertion n k l =
      (ρ_ (𝟙_ (Complex A))).hom := by
  unfold Operad.composeFirstInputInsertion
  change (𝟙 (𝟙_ (Complex A)) ▷ 𝟙_ (Complex A)) ≫
    (λ_ (𝟙_ (Complex A))).hom ≫ 𝟙 _ = _
  simp [unitors_equal]

/-- 可換オペラッドの反復合成は、単位族を一つに縮約する射である。 -/
lemma commutativeComposeFirstInputs_eq (n k : ℕ) (s : Fin n → ℕ) :
    (commutativeOperad A).composeFirstInputs n k s =
      ((𝟙_ (Complex A)) ◁ (tensorUnitFamilyIso A n).hom) ≫
        (ρ_ (𝟙_ (Complex A))).hom := by
  induction n generalizing k with
  | zero =>
    simp only [Operad.composeFirstInputs, tensorUnitFamilyIso, Iso.refl_hom,
      whiskerLeft_id, Fin.sum_univ_zero, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  | succ n ih =>
    rw [Operad.composeFirstInputs_oneSlot_after_factor, commutativeInsertion_eq,
      ih (k + s (Fin.last n)) (fun j => s j.castSucc)]
    change ((𝟙_ (Complex A)) ◁ (tensorFamilySplitLast n
      (fun _ => 𝟙_ (Complex A))).hom) ≫
        tensorSubstitutionStep (ρ_ (𝟙_ (Complex A))).hom
          (((𝟙_ (Complex A)) ◁ (tensorUnitFamilyIso A n).hom) ≫
            (ρ_ (𝟙_ (Complex A))).hom) ≫ 𝟙 _ = _
    rw [Category.comp_id, tensorUnitFamilyIso_succ_hom]
    unfold tensorSubstitutionStep
    simp only [whiskerLeft_comp, Category.assoc]
    have h := tensorSubstitution_rightUnit (tensorUnitFamilyIso A n).hom
      (𝟙 (𝟙_ (Complex A)))
    simp only [Category.comp_id] at h
    rw [h]
    simp only [whiskerLeft_comp, Category.assoc]

end SerrePositivity.EInfinity
