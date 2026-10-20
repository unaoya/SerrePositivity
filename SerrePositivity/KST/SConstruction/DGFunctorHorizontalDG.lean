module
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalUnit
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalInterchange

/-! # 元の横合成の dg 関手化
概要：全次数 Hom end の横合成を tensor dg 関手圏からの dg 関手に束ねる。
方針：四つの純斉次成分で合成保存を判定し、符号つき交換律を使う。
規約：元の横合成 chain map を保持する。使われ方：厳密 dg 入力の豊穣合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

private lemma tensorQuadComposition {A : Type u} [CommRing A]
    {P Q R S T U X Y Z : Complex A}
    (μ : (P ⊗ Q) ⊗ (R ⊗ S) ⟶ T ⊗ U) (h : T ⊗ U ⟶ Z)
    (f : P ⊗ Q ⟶ X) (g : R ⊗ S ⟶ Y) (ν : X ⊗ Y ⟶ Z)
    (hc : ∀ (p q r s n : ℤ) (hn : (p + q) + (r + s) = n)
      (a : P.X p) (b : Q.X q) (c' : R.X r) (d' : S.X s),
      h.f n (μ.f n (ιTensorObj (P ⊗ Q) (R ⊗ S) (p + q) (r + s) n hn
        ((ιTensorObj P Q p q (p + q) rfl (a ⊗ₜ[A] b)) ⊗ₜ[A]
          (ιTensorObj R S r s (r + s) rfl (c' ⊗ₜ[A] d'))))) =
      ν.f n (ιTensorObj X Y (p + q) (r + s) n hn
        (f.f (p + q) (ιTensorObj P Q p q (p + q) rfl (a ⊗ₜ[A] b)) ⊗ₜ[A]
          g.f (r + s) (ιTensorObj R S r s (r + s) rfl (c' ⊗ₜ[A] d'))))) :
    μ ≫ h = (f ⊗ₘ g) ≫ ν := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply SerrePositivity.cochainTensorQuad_hom_ext
  intro p q r s hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_fourfold'
  intro a b c d
  change h.f n (μ.f n
      (SerrePositivity.cochainTensorQuadι P Q R S p q r s n hn
        ((a ⊗ₜ[A] b) ⊗ₜ[A] (c ⊗ₜ[A] d)))) =
    ν.f n ((f ⊗ₘ g).f n
      (SerrePositivity.cochainTensorQuadι P Q R S p q r s n hn
        ((a ⊗ₜ[A] b) ⊗ₜ[A] (c ⊗ₜ[A] d))))
  rw [SerrePositivity.cochainTensorQuadι_apply]
  exact (hc p q r s n (by omega) a b c d).trans
    (congrArg (fun z => ν.f n z) (tensorMap_apply f g (p + q) (r + s) n (by omega)
      (ιTensorObj P Q p q (p + q) rfl (a ⊗ₜ[A] b))
      (ιTensorObj R S r s (r + s) rfl (c ⊗ₜ[A] d)))).symm

/-- tensor dg 圏からの Hom 写像の合成保存を四つの純斉次元で判定する。 -/
lemma dgTensorComposition_of_elements {A : Type u} [CommRing A]
    {C D E : Type*} [DGCategory A C] [DGCategory A D] [DGCategory A E]
    (x y z : DGTensorCategory A C D) (X Y Z : E)
    (f : (x ⟶[Complex A] y) ⟶ (X ⟶[Complex A] Y))
    (g : (y ⟶[Complex A] z) ⟶ (Y ⟶[Complex A] Z))
    (h : (x ⟶[Complex A] z) ⟶ (X ⟶[Complex A] Z))
    (hc : ∀ (p q r s n : ℤ) (hn : (p + q) + (r + s) = n)
      (a : GradedHom A x.1 y.1 p) (b : GradedHom A x.2 y.2 q)
      (c : GradedHom A y.1 z.1 r) (d : GradedHom A y.2 z.2 s),
      h.f n (forward A (dgTensorElement A a b rfl) (dgTensorElement A c d rfl) hn) =
        forward A (f.f (p + q) (dgTensorElement A a b rfl))
          (g.f (r + s) (dgTensorElement A c d rfl)) hn) :
    eComp (Complex A) x y z ≫ h = (f ⊗ₘ g) ≫ eComp (Complex A) X Y Z :=
  tensorQuadComposition (eComp (Complex A) x y z) h f g (eComp (Complex A) X Y Z) hc

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (B : Type t) [DGCategory A B]

local instance horizontalSourceEnrichment :
    DGCategory A (DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B)) :=
  dgTensorEnrichment A (DGFunctor A D E) (DGFunctor A E B)

private lemma map_unit_smul {A : Type u} [CommRing A] {M N : ModuleCat.{u} A}
    (f : M ⟶ N) (c : ℤˣ) (z : M) : f (c • z) = c • f z := by
  simp only [Units.smul_def, map_zsmul]

/-- 横合成は tensor dg 圏の四つの元の斉次成分の合成を保存する。 -/
lemma dgFunctorHorizontal_tensor_forward
    {x y z : DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B)}
    {p q r s n : ℤ} (a : GradedHom A x.1 y.1 p) (b : GradedHom A x.2 y.2 q)
    (c : GradedHom A y.1 z.1 r) (d : GradedHom A y.2 z.2 s)
    (hn : (p + q) + (r + s) = n) :
    (dgFunctorHorizontal A D E B x.1 z.1 x.2 z.2).f n
        (forward A (dgTensorElement A a b rfl) (dgTensorElement A c d rfl) hn) =
      forward A (dgFunctorHorizontalElement A D E B a b rfl)
        (dgFunctorHorizontalElement A D E B c d rfl) hn := by
  have h := congrArg (fun v =>
    (dgFunctorHorizontal A D E B x.1 z.1 x.2 z.2).f n v)
    (dgTensor_forward A (x := x) (y := y) (z := z) a b c d hn)
  exact h.trans ((map_unit_smul _ _ _).trans
    (dgFunctorHorizontalElement_interchange A D E B a b c d hn).symm)

/-- 横合成は、元の tensor dg 圏の豊穣合成を厳密に保つ。 -/
lemma dgFunctorHorizontal_tensor_composition
    (x y z : DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B)) :
    eComp (Complex A) x y z ≫ dgFunctorHorizontal A D E B x.1 z.1 x.2 z.2 =
      (dgFunctorHorizontal A D E B x.1 y.1 x.2 y.2 ⊗ₘ
        dgFunctorHorizontal A D E B y.1 z.1 y.2 z.2) ≫
          dgFunctorComposition A D B (x.1.comp x.2) (y.1.comp y.2) (z.1.comp z.2) := by
  exact dgTensorComposition_of_elements x y z (x.1.comp x.2) (y.1.comp y.2) (z.1.comp z.2)
    (dgFunctorHorizontal A D E B x.1 y.1 x.2 y.2)
    (dgFunctorHorizontal A D E B y.1 z.1 y.2 z.2)
    (dgFunctorHorizontal A D E B x.1 z.1 x.2 z.2)
    (fun _ _ _ _ _ hn a b c d =>
      dgFunctorHorizontal_tensor_forward A D E B (x := x) (y := y) (z := z) a b c d hn)

/-- 全次数の元の横合成による厳密 dg 関手。 -/
def dgFunctorHorizontalDG :
    DGFunctor A (DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B))
      (DGFunctor A D B) where
  obj x := x.1.comp x.2
  map x y := dgFunctorHorizontal A D E B x.1 y.1 x.2 y.2
  map_id x := dgFunctorHorizontal_tensor_identity A D E B x.1 x.2
  map_comp x y z := dgFunctorHorizontal_tensor_composition A D E B x y z

end SerrePositivity.KST.SConstruction
