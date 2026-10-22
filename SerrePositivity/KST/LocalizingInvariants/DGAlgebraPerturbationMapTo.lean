module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPerturbation
public import SerrePositivity.DifferentialGraded.Complexes.PerturbationMap

/-!
概要：追加作用素を消す元の実代数射を、微分変更後の実代数射へ持ち上げる。
方針：元の次数ごとの射を鎖写像にし、元の単位・積保存を同じ斉次元上で回収する。
規約：作用素の零化は実 cochain の等式。使われ方：Postnikov の射影と class。
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
  (hd : IsDerivation A θ) (hu : (Cochain.ofHom η[A.X]).comp θ (zero_add 1) = 0)
  {B : Mon (Complex R)} (f : A ⟶ B)
  (hf : θ.comp (Cochain.ofHom f.hom) (add_zero 1) = 0)

def mapToHom : (algebra A θ hθ hθθ hd hu).X ⟶ B.X :=
  perturbSourceMap A.X B.X θ hθ hθθ (Cochain.ofHom f.hom) (by rw [δ_ofHom, hf])

lemma mapToHom_f (n : ℤ) : (mapToHom A θ hθ hθθ hd hu f hf).f n = f.hom.f n := rfl

lemma mapToHom_one : η[(algebra A θ hθ hθθ hd hu).X] ≫ mapToHom A θ hθ hθθ hd hu f hf =
    η[B.X] := by
  apply HomologicalComplex.hom_ext
  intro n
  exact congrArg (fun t => t.f n) (IsMonHom.one_hom f.hom)

lemma mapToHom_mul : μ[(algebra A θ hθ hθθ hd hu).X] ≫ mapToHom A θ hθ hθθ hd hu f hf =
    (mapToHom A θ hθ hθθ hd hu f hf ⊗ₘ mapToHom A θ hθ hθθ hd hu f hf) ≫ μ[B.X] := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  let g := mapToHom A θ hθ hθθ hd hu f hf
  change g.f n ((mul A θ hθ hθθ hd).f n
    (ιTensorObj (obj A θ hθ hθθ) (obj A θ hθ hθθ) p q n hpq (a ⊗ₜ[R] b))) =
    μ[B.X].f n ((g ⊗ₘ g).f n
      (ιTensorObj (obj A θ hθ hθθ) (obj A θ hθ hθθ) p q n hpq (a ⊗ₜ[R] b)))
  have hm := congrArg (fun t => t.f n (ιTensorObj A.X A.X p q n hpq (a ⊗ₜ[R] b)))
    (IsMonHom.mul_hom f.hom)
  change f.hom.f n (μ[A.X].f n (ιTensorObj A.X A.X p q n hpq (a ⊗ₜ[R] b))) =
    μ[B.X].f n ((f.hom ⊗ₘ f.hom).f n (ιTensorObj A.X A.X p q n hpq (a ⊗ₜ[R] b))) at hm
  exact (congrArg (fun z => g.f n z) (mul_apply A θ hθ hθθ hd p q n hpq a b)).trans
    (hm.trans ((congrArg (fun z => μ[B.X].f n z) (tensorMap_apply f.hom f.hom p q n hpq a b)).trans
      (congrArg (fun z => μ[B.X].f n z) (tensorMap_apply g g p q n hpq a b)).symm))

def mapTo : algebra A θ hθ hθθ hd hu ⟶ B :=
  Mon.Hom.mk' (mapToHom A θ hθ hθθ hd hu f hf)
    (mapToHom_one A θ hθ hθθ hd hu f hf) (mapToHom_mul A θ hθ hθθ hd hu f hf)

end SerrePositivity.KST.LocalizingInvariants.AlgebraPerturbation
