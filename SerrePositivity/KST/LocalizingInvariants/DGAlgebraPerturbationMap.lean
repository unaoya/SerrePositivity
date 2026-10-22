module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPerturbation

/-!
概要：追加微分を可換にする実代数射を、両側の微分変更後の実代数射へ移す。
方針：元の次数ごとの射を使い、鎖写像条件と単位・積保存を元の等式へ戻す。
規約：作用素との可換性は実 cochain の等式。使われ方：Postnikov 拡大の自然性。
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
variable {R : Type u} [CommRing R] (A B : Mon (Complex R))
  (θ : Cochain A.X A.X 1) (ψ : Cochain B.X B.X 1)
  (hθ : δ 1 2 θ = 0) (hθθ : θ.comp θ (rfl : (1 : ℤ) + 1 = 2) = 0)
  (hψ : δ 1 2 ψ = 0) (hψψ : ψ.comp ψ (rfl : (1 : ℤ) + 1 = 2) = 0)
  (hdθ : IsDerivation A θ) (huθ : (Cochain.ofHom η[A.X]).comp θ (zero_add 1) = 0)
  (hdψ : IsDerivation B ψ) (huψ : (Cochain.ofHom η[B.X]).comp ψ (zero_add 1) = 0)
  (f : A ⟶ B) (hf : θ.comp (Cochain.ofHom f.hom) (add_zero 1) =
    (Cochain.ofHom f.hom).comp ψ (zero_add 1))

def mapHom : (algebra A θ hθ hθθ hdθ huθ).X ⟶ (algebra B ψ hψ hψψ hdψ huψ).X :=
  CochainComplex.ofHom (fun n => f.hom.f n) (fun n => by
    have he := Cochain.congr_v hf n (n + 1) rfl
    simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at he
    change f.hom.f n ≫ (perturbComplex B.X ψ hψ hψψ).d n (n + 1) =
      (perturbComplex A.X θ hθ hθθ).d n (n + 1) ≫ f.hom.f (n + 1)
    rw [perturbComplex_d, perturbComplex_d, Preadditive.comp_add, Preadditive.add_comp,
      f.hom.comm n (n + 1), he])

lemma mapHom_one : η[(algebra A θ hθ hθθ hdθ huθ).X] ≫
    mapHom A B θ ψ hθ hθθ hψ hψψ hdθ huθ hdψ huψ f hf =
      η[(algebra B ψ hψ hψψ hdψ huψ).X] := by
  apply HomologicalComplex.hom_ext
  intro n
  exact congrArg (fun t => t.f n) (IsMonHom.one_hom f.hom)

lemma mapHom_mul : μ[(algebra A θ hθ hθθ hdθ huθ).X] ≫
    mapHom A B θ ψ hθ hθθ hψ hψψ hdθ huθ hdψ huψ f hf =
      (mapHom A B θ ψ hθ hθθ hψ hψψ hdθ huθ hdψ huψ f hf ⊗ₘ
        mapHom A B θ ψ hθ hθθ hψ hψψ hdθ huθ hdψ huψ f hf) ≫
          μ[(algebra B ψ hψ hψψ hdψ huψ).X] := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  change A.X.X p at a
  change A.X.X q at b
  let g : obj A θ hθ hθθ ⟶ obj B ψ hψ hψψ := mapHom A B θ ψ hθ hθθ hψ hψψ hdθ huθ hdψ huψ f hf
  change g.f n ((mul A θ hθ hθθ hdθ).f n
    (ιTensorObj (obj A θ hθ hθθ) (obj A θ hθ hθθ) p q n hpq (a ⊗ₜ[R] b))) =
      (mul B ψ hψ hψψ hdψ).f n ((g ⊗ₘ g).f n
        (ιTensorObj (obj A θ hθ hθθ) (obj A θ hθ hθθ) p q n hpq (a ⊗ₜ[R] b)))
  have hm := ConcreteCategory.congr_hom (congrArg (fun t => t.f n)
    (IsMonHom.mul_hom f.hom)) (ιTensorObj A.X A.X p q n hpq (a ⊗ₜ[R] b))
  change f.hom.f n (μ[A.X].f n (ιTensorObj A.X A.X p q n hpq (a ⊗ₜ[R] b))) =
    μ[B.X].f n ((f.hom ⊗ₘ f.hom).f n (ιTensorObj A.X A.X p q n hpq (a ⊗ₜ[R] b))) at hm
  rw [tensorMap_apply] at hm
  exact (congrArg (fun z => g.f n z) (mul_apply A θ hθ hθθ hdθ p q n hpq a b)).trans
    (hm.trans ((mul_apply B ψ hψ hψψ hdψ p q n hpq (g.f p a) (g.f q b)).symm.trans
      (congrArg (fun z => (mul B ψ hψ hψψ hdψ).f n z)
        (tensorMap_apply g g p q n hpq a b)).symm))

def map : algebra A θ hθ hθθ hdθ huθ ⟶ algebra B ψ hψ hψψ hdψ huψ :=
  Mon.Hom.mk' (mapHom A B θ ψ hθ hθθ hψ hψψ hdθ huθ hdψ huψ f hf)
    (mapHom_one A B θ ψ hθ hθθ hψ hψψ hdθ huθ hdψ huψ f hf)
    (mapHom_mul A B θ ψ hθ hθθ hψ hψψ hdθ huθ hdψ huψ f hf)

end SerrePositivity.KST.LocalizingInvariants.AlgebraPerturbation
