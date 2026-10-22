module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPerturbation

/-!
概要：像を追加作用素が消す実代数射を、微分変更後の実代数射へ移送する。
方針：次数ごとの元の射を鎖写像とし、元の積保存を同じ純 tensor 上で回収する。
規約：微分との可換性も証明する。使われ方：Postnikov の元の上段代数の包含。
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
  {B : Mon (Complex R)} (f : B ⟶ A)
  (hf : (Cochain.ofHom f.hom).comp θ (zero_add 1) = 0)

def mapFromHom : B.X ⟶ (algebra A θ hθ hθθ hd hu).X :=
  CochainComplex.ofHom (fun n => f.hom.f n) (fun n => by
    have he := Cochain.congr_v hf n (n + 1) rfl
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] at he
    change f.hom.f n ≫ (perturbComplex A.X θ hθ hθθ).d n (n + 1) = _
    rw [perturbComplex_d, Preadditive.comp_add, he, add_zero]
    exact f.hom.comm n (n + 1))

lemma mapFromHom_one : η[B.X] ≫ mapFromHom A θ hθ hθθ hd hu f hf =
    η[(algebra A θ hθ hθθ hd hu).X] := by
  apply HomologicalComplex.hom_ext
  intro n
  exact congrArg (fun t => t.f n) (IsMonHom.one_hom f.hom)

lemma mapFromHom_mul : μ[B.X] ≫ mapFromHom A θ hθ hθθ hd hu f hf =
    (mapFromHom A θ hθ hθθ hd hu f hf ⊗ₘ mapFromHom A θ hθ hθθ hd hu f hf) ≫
      μ[(algebra A θ hθ hθθ hd hu).X] := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  let g := mapFromHom A θ hθ hθθ hd hu f hf
  change f.hom.f n (μ[B.X].f n (ιTensorObj B.X B.X p q n hpq (a ⊗ₜ[R] b))) =
    (mul A θ hθ hθθ hd).f n ((g ⊗ₘ g).f n
      (ιTensorObj B.X B.X p q n hpq (a ⊗ₜ[R] b)))
  have hm := congrArg (fun t => t.f n (ιTensorObj B.X B.X p q n hpq (a ⊗ₜ[R] b)))
    (IsMonHom.mul_hom f.hom)
  change f.hom.f n (μ[B.X].f n (ιTensorObj B.X B.X p q n hpq (a ⊗ₜ[R] b))) =
    μ[A.X].f n ((f.hom ⊗ₘ f.hom).f n (ιTensorObj B.X B.X p q n hpq (a ⊗ₜ[R] b))) at hm
  have ht := tensorMap_apply f.hom f.hom p q n hpq a b
  have hn := tensorMap_apply g g p q n hpq a b
  exact (hm.trans (congrArg (fun z => μ[A.X].f n z) ht)).trans
    ((mul_apply A θ hθ hθθ hd p q n hpq (f.hom.f p a) (f.hom.f q b)).symm.trans
      (congrArg (fun z => (mul A θ hθ hθθ hd).f n z) hn).symm)

def mapFrom : B ⟶ algebra A θ hθ hθθ hd hu :=
  Mon.Hom.mk' (mapFromHom A θ hθ hθθ hd hu f hf)
    (mapFromHom_one A θ hθ hθθ hd hu f hf) (mapFromHom_mul A θ hθ hθθ hd hu f hf)

end SerrePositivity.KST.LocalizingInvariants.AlgebraPerturbation
