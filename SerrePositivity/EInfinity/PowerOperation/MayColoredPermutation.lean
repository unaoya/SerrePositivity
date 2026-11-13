module

public import SerrePositivity.EInfinity.PowerOperation.MayColoredValues
public import SerrePositivity.EInfinity.PowerOperation.MayWordAdjacent
public import SerrePositivity.EInfinity.PowerOperation.MayHomogeneousSwap

/-!
# May の同次二色入力と実隣接交換

May, Proposition 2.3(ii) の混合項の前段。
二色語の置換と、元のテンソル冪の Koszul 交換を同じ入力上で照合する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers SerrePositivity.Coxeter
variable {k : Type u} [CommRing k]

lemma mayColoredValue_cons (K : Complex k) (q : ℤ) (a b : K.X q)
    (n : ℕ) (c : Bool) (w : BinaryTensorWord n) :
    mayColoredValue K q a b (n + 1) (mayWordCons n c w) =
      ιTensorObj K (power K n) q (mayRepeatedDegree q n) (mayRepeatedDegree q (n + 1)) rfl
        ((if c then b else a) ⊗ₜ[k] mayColoredValue K q a b n w) := by
  cases c <;> rfl

/-- 混合入力の同じ隣接交換は、語を交換して同じ Koszul 符号を掛ける。 -/
lemma mayColoredValue_adjacent (K : Complex k) (q : ℤ) (a b : K.X q)
    (n : ℕ) (i : Fin n) (w : BinaryTensorWord (n + 1)) :
    (adjacentIso K n i).hom.f (mayRepeatedDegree q (n + 1))
      (mayColoredValue K q a b (n + 1) w) =
        (q * q).negOnePow • mayColoredValue K q a b (n + 1) (adjacentTransposition i • w) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨c, v, rfl⟩ := mayWordCons_surjective (n + 1) w
      obtain ⟨d, v, rfl⟩ := mayWordCons_surjective n v
      rw [mayWordCons_swapFirst, mayColoredValue_cons, mayColoredValue_cons,
        mayColoredValue_cons, mayColoredValue_cons]
      exact mayHomogeneousSwapFirst K q _ _ n (mayColoredValue K q a b n v)
    · obtain ⟨c, v, rfl⟩ := mayWordCons_surjective (n + 1) w
      rw [mayWordCons_swapTail, mayColoredValue_cons, mayColoredValue_cons]
      change (cochainTensorMap (𝟙 K) (adjacentIso K n j).hom).f _
        (ιTensorObj K (power K (n + 1)) q (mayRepeatedDegree q (n + 1)) _ rfl
          (_ ⊗ₜ[k] mayColoredValue K q a b (n + 1) v)) = _
      rw [cochainTensorMap_apply_ι]
      simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
      rw [ih j v]
      simp only [Units.smul_def, TensorProduct.tmul_smul]
      change (ιTensorObj K (power K (n + 1)) _ _ _ _).hom
        ((↑(q * q).negOnePow : ℤ) • _) = _
      rw [map_zsmul]
      rfl

end SerrePositivity.EInfinity.PowerOperation
