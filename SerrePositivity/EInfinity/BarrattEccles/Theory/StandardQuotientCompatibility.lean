module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.WordQuotientTransport

/-!
# 標準語の分離と指定全複体商

HA 3.2.4.7 の自由比較で、標準代表を左右の冪へ移す同型の指定商を照合する。
BS-W16 の型一覧 L05。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory HomologicalComplex Limits
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
attribute [local instance] Classical.propDecidable
variable (R : Type u) [CommRing R] (X Y : Complex R)

set_option maxHeartbeats 800000 in
-- 制限した作用と標準語の表現複体を同時に照合するため計算上限を広げる。
/-- 標準語の群変更と分離は、同じ指定全複体商を保つ。 -/
lemma orbitStandardCoefficientIso_quotient (m n : ℕ) :
    coinvariantTotalQuotient
      (binaryTensorWordFixedAction X Y (m + n) (binaryTensorCountPattern (m + n) ⟨m, by omega⟩)
        ((MulEquiv.ulift : ULift.{u} (Equiv.Perm (Fin (m + n))) ≃*
          Equiv.Perm (Fin (m + n))).toMonoidHom.comp
            (binaryTensorPatternSubgroup (m + n) (ULift.up ⟨m, by omega⟩)).subtype)
        (fun g => g.property))
      ((arityComplexAction R (m + n)).comp
        (binaryTensorPatternSubgroup (m + n) (ULift.up ⟨m, by omega⟩)).subtype) ≫
      (orbitStandardCoefficientIso X Y m n).hom =
    ((eqToHom (congrArg (binaryTensorWordObj X Y (m + n))
      (binaryTensorCountPattern_add m n)) ≫ (binaryTensorStandardPowersIso X Y m n).hom) ▷
        (operad R).arity (m + n)) ≫
    coinvariantTotalQuotient
      (tensorComplexAction (twoColorLeftInputAction X m n) (twoColorRightInputAction Y m n))
      (twoColorSourceComplexAction R m n) := by
  let k : ULift.{u} (Fin (m + n + 1)) := ULift.up ⟨m, by omega⟩
  let e := (binaryTensorPatternGroupEquiv m n).symm
  let ρ := binaryTensorWordFixedAction X Y (m + n) (binaryTensorCountPattern (m + n) k.down)
    ((MulEquiv.ulift : ULift.{u} (Equiv.Perm (Fin (m + n))) ≃*
      Equiv.Perm (Fin (m + n))).toMonoidHom.comp (binaryTensorPatternSubgroup (m + n) k).subtype)
    (fun g => g.property)
  let σ := (arityComplexAction R (m + n)).comp (binaryTensorPatternSubgroup (m + n) k).subtype
  rw [← coinvariantTotalGroupChangeIso_quotient e ρ σ]
  dsimp only [orbitStandardCoefficientIso, k, e, ρ, σ]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.app_hom, Functor.mapIso_hom]
  change _ ≫ (inputCoinvariantTotalFunctor (twoColorSourceCochain R m n)).map
    ((twoColorOrbitStandardInputIso X Y m n).hom ≫
      (twoColorStandardSeparatedIso X Y m n).hom) = _
  simp only [twoColorOrbitStandardInputIso, twoColorOrbitRestrictionIso, Iso.trans_hom,
    Iso.refl_hom, Category.id_comp, Functor.map_comp]
  erw [reassoc_of% (coinvariantTotalQuotient_wordCongr X Y
    (binaryTensorCountPattern_add m n) (twoColorInputPermutation m n)
    (twoColorCountPattern_fixed m n) (twoColorInputPermutation_fixed m n)
    (twoColorSourceComplexAction R m n))]
  simp only [twoColorStandardSeparatedIso, representationCochainIso]
  erw [coinvariantTotalQuotient_naturality_left
    (binaryTensorWordFixedAction X Y (m + n) (binaryTensorStandardPattern m n)
      (twoColorInputPermutation m n) (twoColorInputPermutation_fixed m n))
    (tensorComplexAction (twoColorLeftInputAction X m n) (twoColorRightInputAction Y m n))
    (twoColorSourceComplexAction R m n) (binaryTensorStandardPowersIso X Y m n).hom
    (twoColorStandardPowersIso_action X Y m n)]
  simp only [comp_whiskerRight, Category.assoc]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
