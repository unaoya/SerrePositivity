module
public import SerrePositivity.DifferentialGraded.Complexes.Currying
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorReindex

/-! # 二重転置の全次数評価式 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma curryRight_twice_apply {K P Q T : Complex A} (a : (K ⊗ P) ⊗ Q ⟶ T)
    {k r l s n : ℤ} (hl : r + k = l) (hn : s + l = n)
    (z : K.X k) (m : P.X r) (v : Q.X s) :
    (((curryRight (curryRight a)).f k z).v r l hl m).v s n hn v =
      a.f n (ιTensorObj (K ⊗ P) Q l s n (by omega)
        (ιTensorObj K P k r l (by omega) (z ⊗ₜ[A] m) ⊗ₜ[A] v)) := rfl

lemma curryRight_associator_apply {K P Q S T : Complex A} (i : P ⊗ Q ⟶ S)
    (f : K ⟶ homComplex A S T) {k r l s n : ℤ}
    (hl : r + k = l) (hn : s + l = n) (z : K.X k) (m : P.X r) (v : Q.X s) :
    (((curryRight (curryRight ((α_ K P Q).hom ≫ ((K ◁ i) ≫ uncurryRight f)))).f k z).v
      r l hl m).v s n hn v =
    (f.f k z).v (r + s) n (by omega) (i.f (r + s) (ιTensorObj P Q r s (r + s) rfl
      (m ⊗ₜ[A] v))) := by
  rw [curryRight_twice_apply]
  change (uncurryRight f).f n ((K ◁ i).f n ((α_ K P Q).hom.f n
    (ιTensorObj (K ⊗ P) Q l s n (by omega)
      (ιTensorObj K P k r l (by omega) (z ⊗ₜ[A] m) ⊗ₜ[A] v)))) = _
  rw [associator_apply_of_sums K P Q k r s l (r + s) n (by omega) rfl (by omega),
    whiskerLeft_apply, uncurryRight_apply]

end SerrePositivity.DifferentialGraded
