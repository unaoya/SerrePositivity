module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPerturbedMultiplication
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin


/-!
概要：単位を消す閉じた平方零 derivation に沿う微分変更を、実 dg 代数にする。
方針：単位と積を鎖写像として構成し、斉次元上で元の単位則・結合則に戻す。
規約：全次数・非可換積。使われ方：層包含を追加微分とする Postnikov cone 代数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.AlgebraPerturbation
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) (θ : Cochain A.X A.X 1)
  (hθ : δ 1 2 θ = 0) (hθθ : θ.comp θ (rfl : (1 : ℤ) + 1 = 2) = 0)
  (hd : IsDerivation A θ)
  (hu : (Cochain.ofHom η[A.X]).comp θ (zero_add 1) = 0)

def one : 𝟙_ (Complex R) ⟶ obj A θ hθ hθθ :=
  CochainComplex.ofHom (fun n => η[A.X].f n) (fun n => by
    have h := Cochain.congr_v hu n (n + 1) rfl
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] at h
    rw [perturbComplex_d, Preadditive.comp_add, h, add_zero]
    exact η[A.X].comm n (n + 1))

lemma one_f (n : ℤ) : (one A θ hθ hθθ hu).f n = η[A.X].f n := rfl

lemma one_mul : (one A θ hθ hθθ hu ▷ obj A θ hθ hθθ) ≫ mul A θ hθ hθθ hd =
    (λ_ (obj A θ hθ hθθ)).hom := by
  apply (cancel_epi (λ_ (obj A θ hθ hθθ)).inv).1
  rw [Iso.inv_hom_id]
  apply chain_ext_apply
  intro n a
  let u := (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv (1 : R)
  have h : (λ_ A.X).inv ≫ (η[A.X] ▷ A.X) ≫ μ[A.X] = 𝟙 A.X := by
    rw [MonObj.one_mul, Iso.inv_hom_id]
  have hv := congrArg (fun f => f.f n a) h
  change μ[A.X].f n ((η[A.X] ▷ A.X).f n ((λ_ A.X).inv.f n a)) = a at hv
  rw [complexLeftUnitor_inv_apply] at hv
  have hw := whiskerRight_apply η[A.X] A.X 0 n n (zero_add n) u a
  have hold := (congrArg (fun z => μ[A.X].f n z) hw).symm.trans hv
  change (mul A θ hθ hθθ hd).f n ((one A θ hθ hθθ hu ▷ obj A θ hθ hθθ).f n
    ((λ_ (obj A θ hθ hθθ)).inv.f n a)) = a
  rw [complexLeftUnitor_inv_apply]
  have hn := whiskerRight_apply (one A θ hθ hθθ hu) (obj A θ hθ hθθ)
    0 n n (zero_add n) u a
  exact ((congrArg (fun z => (mul A θ hθ hθθ hd).f n z) hn).trans
    (mul_apply A θ hθ hθθ hd 0 n n (zero_add n) _ a)).trans hold

lemma mul_one : (obj A θ hθ hθθ ◁ one A θ hθ hθθ hu) ≫ mul A θ hθ hθθ hd =
    (ρ_ (obj A θ hθ hθθ)).hom := by
  apply (cancel_epi (ρ_ (obj A θ hθ hθθ)).inv).1
  rw [Iso.inv_hom_id]
  apply chain_ext_apply
  intro n a
  let u := (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv (1 : R)
  have h : (ρ_ A.X).inv ≫ (A.X ◁ η[A.X]) ≫ μ[A.X] = 𝟙 A.X := by
    rw [MonObj.mul_one, Iso.inv_hom_id]
  have hv := congrArg (fun f => f.f n a) h
  change μ[A.X].f n ((A.X ◁ η[A.X]).f n ((ρ_ A.X).inv.f n a)) = a at hv
  rw [complexRightUnitor_inv_apply] at hv
  have hw := whiskerLeft_apply A.X η[A.X] n 0 n (add_zero n) a u
  have hold := (congrArg (fun z => μ[A.X].f n z) hw).symm.trans hv
  change (mul A θ hθ hθθ hd).f n ((obj A θ hθ hθθ ◁ one A θ hθ hθθ hu).f n
    ((ρ_ (obj A θ hθ hθθ)).inv.f n a)) = a
  rw [complexRightUnitor_inv_apply]
  have hn := whiskerLeft_apply (obj A θ hθ hθθ) (one A θ hθ hθθ hu)
    n 0 n (add_zero n) a u
  exact ((congrArg (fun z => (mul A θ hθ hθθ hd).f n z) hn).trans
    (mul_apply A θ hθ hθθ hd n 0 n (add_zero n) a _)).trans hold

lemma mul_assoc : (mul A θ hθ hθθ hd ▷ obj A θ hθ hθθ) ≫ mul A θ hθ hθθ hd =
    (α_ (obj A θ hθ hθθ) (obj A θ hθ hθθ) (obj A θ hθ hθθ)).hom ≫
      (obj A θ hθ hθθ ◁ mul A θ hθ hθθ hd) ≫ mul A θ hθ hθθ hd := by
  apply tensorComposition_assoc_of_apply
  intro p q r n hn a b c
  simp only [mul_apply]
  exact tensorComposition_assoc_apply A.X A.X A.X A.X A.X A.X
    μ[A.X] μ[A.X] μ[A.X] μ[A.X] (MonObj.mul_assoc A.X) p q r n hn a b c

def algebra : Mon (Complex R) where
  X := obj A θ hθ hθθ
  mon := {
    one := one A θ hθ hθθ hu
    mul := mul A θ hθ hθθ hd
    one_mul := one_mul A θ hθ hθθ hd hu
    mul_one := mul_one A θ hθ hθθ hd hu
    mul_assoc := mul_assoc A θ hθ hθθ hd }

end SerrePositivity.KST.LocalizingInvariants.AlgebraPerturbation
