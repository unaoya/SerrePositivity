module

public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
概要：実余モノイドから dg 代数の内部 Hom 畳み込みを構成する。
方針：tensor の oplax 構造と右随伴による転置を使う。
規約：構造は明示的に選び、大域 instance と KST への依存を追加しない。
使われ方：AW 区間の実 dg 代数 path object と転送モデル構造。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex
open scoped ComonObj MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.EInfinity.DGAlgebra
variable (R : Type u) [CommRing R] (H : Comon (Complex R))

local instance : MonoidalCategory (Complex R × Complex R) :=
  MonoidalCategory.prodMonoidal (Complex R) (Complex R)

/-- 概要：畳み込みの coalgebraConstant を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
def coalgebraConstant : Complex R ⥤ Complex R :=
  (Functor.const (Complex R)).obj H.X

/-- 概要：畳み込みの coalgebraConstant_oplax を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
@[instance_reducible]
def coalgebraConstant_oplax : (coalgebraConstant R H).OplaxMonoidal where
  «η» := ε[H.X]
  δ _ _ := Δ[H.X]
  δ_natural_left _ _ := by simp [coalgebraConstant]
  δ_natural_right _ _ := by simp [coalgebraConstant]
  oplax_associativity _ _ _ := by
    simp [coalgebraConstant]
  oplax_left_unitality _ := by
    simp [coalgebraConstant]
  oplax_right_unitality _ := by
    simp [coalgebraConstant]

/-- 概要：畳み込みの coalgebraTensor を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
def coalgebraTensor : Complex R ⥤ Complex R :=
  (Functor.prod' (coalgebraConstant R H) (𝟭 (Complex R))) ⋙ tensor (Complex R)

/-- 概要：畳み込みの coalgebraTensor_oplax を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
@[instance_reducible]
def coalgebraTensor_oplax : (coalgebraTensor R H).OplaxMonoidal := by
  letI : (coalgebraConstant R H).OplaxMonoidal := coalgebraConstant_oplax R H
  letI : (Functor.prod' (coalgebraConstant R H) (𝟭 (Complex R))).OplaxMonoidal := inferInstance
  letI : (tensor (Complex R)).Monoidal := inferInstance
  unfold coalgebraTensor
  infer_instance

attribute [local instance] coalgebraConstant_oplax coalgebraTensor_oplax

/-- 概要：畳み込みの coalgebraTensorIso を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
def coalgebraTensorIso : tensorLeft H.X ≅ coalgebraTensor R H :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    simp [coalgebraTensor, coalgebraConstant])

/-- 概要：畳み込みの coalgebraHomAdjunction を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
def coalgebraHomAdjunction : coalgebraTensor R H ⊣ ihom H.X :=
  (ihom.adjunction H.X).ofNatIsoLeft (coalgebraTensorIso R H)

/-- 概要：畳み込みの coalgebraHomLax を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
@[instance_reducible]
def coalgebraHomLax : (ihom H.X).LaxMonoidal :=
  (coalgebraHomAdjunction R H).rightAdjointLaxMonoidal

attribute [local instance] coalgebraHomLax

/-- 概要：畳み込みの convolutionAlgebraFunctor を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
def convolutionAlgebraFunctor : Mon (Complex R) ⥤ Mon (Complex R) :=
  (ihom H.X).mapMon

/-- 概要：畳み込みの convolutionAlgebraFunctor_obj_X を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma convolutionAlgebraFunctor_obj_X (B : Mon (Complex R)) :
    ((convolutionAlgebraFunctor R H).obj B).X = (ihom H.X).obj B.X := rfl

/-- 概要：畳み込みの convolutionAlgebraFunctor_map_hom を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma convolutionAlgebraFunctor_map_hom {B C : Mon (Complex R)} (f : B ⟶ C) :
    ((convolutionAlgebraFunctor R H).map f).hom = (ihom H.X).map f.hom := rfl

/-- 概要：畳み込みの convolutionAlgebraFunctor_obj_homComplex を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma convolutionAlgebraFunctor_obj_homComplex (B : Mon (Complex R)) :
    ((convolutionAlgebraFunctor R H).obj B).X = homComplex R H.X B.X := rfl

/-- 概要：畳み込みの convolutionAlgebraFunctor_one を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma convolutionAlgebraFunctor_one (B : Mon (Complex R)) :
    η[((convolutionAlgebraFunctor R H).obj B).X] =
      (coalgebraHomAdjunction R H).homEquiv _ _
        (Functor.OplaxMonoidal.η (coalgebraTensor R H) ≫ B.mon.one) := by
  change (coalgebraHomAdjunction R H).homEquiv _ _ _ ≫ (ihom H.X).map B.mon.one = _
  exact ((coalgebraHomAdjunction R H).homEquiv_naturality_right _ _).symm

/-- 概要：畳み込みの convolutionAlgebraFunctor_mul を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma convolutionAlgebraFunctor_mul (B : Mon (Complex R)) :
    μ[((convolutionAlgebraFunctor R H).obj B).X] =
      (coalgebraHomAdjunction R H).homEquiv _ _
        (Functor.OplaxMonoidal.δ (coalgebraTensor R H)
          ((ihom H.X).obj B.X) ((ihom H.X).obj B.X) ≫
          ((coalgebraHomAdjunction R H).counit.app B.X ⊗ₘ
            (coalgebraHomAdjunction R H).counit.app B.X) ≫ B.mon.mul) := by
  change (coalgebraHomAdjunction R H).homEquiv _ _ _ ≫ (ihom H.X).map B.mon.mul = _
  simpa only [CategoryTheory.Functor.id_obj, Category.assoc] using
    ((coalgebraHomAdjunction R H).homEquiv_naturality_right
    (Functor.OplaxMonoidal.δ (coalgebraTensor R H)
      ((ihom H.X).obj B.X) ((ihom H.X).obj B.X) ≫
      ((coalgebraHomAdjunction R H).counit.app B.X ⊗ₘ
        (coalgebraHomAdjunction R H).counit.app B.X)) B.mon.mul).symm


end SerrePositivity.EInfinity.DGAlgebra
