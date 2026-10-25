module

public import SerrePositivity.EInfinity.DGAlgebra.ConvolutionCounit

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
attribute [local instance] coalgebraConstant_oplax coalgebraTensor_oplax coalgebraHomLax

variable (R : Type u) [CommRing R] (H : Comon (Complex R)) (B : Mon (Complex R))

/-- 概要：畳み込みの convolutionUnitHom を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
def convolutionUnitHom : B.X ⟶ ((convolutionAlgebraFunctor R H).obj B).X :=
  MonoidalClosed.curry (A := H.X) ((coalgebraTensorCounit R H).app B.X)

/-- 概要：畳み込みの convolutionUnitHom_one を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma convolutionUnitHom_one :
    B.mon.one ≫ convolutionUnitHom R H B = η[((convolutionAlgebraFunctor R H).obj B).X] := by
  rw [convolutionUnitHom, ← MonoidalClosed.curry_natural_left,
    convolutionAlgebraFunctor_one, coalgebraHomAdjunction_homEquiv]
  congr 1
  have h : H.X ◁ B.mon.one ≫ (coalgebraTensorCounit R H).app B.X =
      (coalgebraTensorCounit R H).app (𝟙_ (Complex R)) ≫ B.mon.one := by
    exact (coalgebraTensorCounit R H).naturality B.mon.one
  rw [h, coalgebraTensorCounit_unit]

/-- 概要：畳み込みの convolutionUnitHom_mul を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma convolutionUnitHom_mul :
    B.mon.mul ≫ convolutionUnitHom R H B =
      (convolutionUnitHom R H B ⊗ₘ convolutionUnitHom R H B) ≫
        μ[((convolutionAlgebraFunctor R H).obj B).X] := by
  let p : B.X ⟶ (ihom H.X).obj B.X := convolutionUnitHom R H B
  have hn : H.X ◁ (p ⊗ₘ p) ≫ Functor.OplaxMonoidal.δ (coalgebraTensor R H)
      ((ihom H.X).obj B.X) ((ihom H.X).obj B.X) =
      Functor.OplaxMonoidal.δ (coalgebraTensor R H) B.X B.X ≫
        (H.X ◁ p ⊗ₘ H.X ◁ p) := by
    exact (Functor.OplaxMonoidal.δ_natural (coalgebraTensor R H) p p).symm
  have he : H.X ◁ p ≫ (ihom.ev H.X).app B.X = (coalgebraTensorCounit R H).app B.X :=
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app (A := H.X) B.X
      ((coalgebraTensorCounit R H).app B.X)
  have hb : H.X ◁ B.mon.mul ≫ (coalgebraTensorCounit R H).app B.X =
      (coalgebraTensorCounit R H).app (B.X ⊗ B.X) ≫ B.mon.mul := by
    exact (coalgebraTensorCounit R H).naturality B.mon.mul
  have hp : MonoidalClosed.uncurry p = (coalgebraTensorCounit R H).app B.X :=
    MonoidalClosed.uncurry_curry (A := H.X) ((coalgebraTensorCounit R H).app B.X)
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    convolutionAlgebraFunctor_mul, coalgebraHomAdjunction_homEquiv,
    MonoidalClosed.uncurry_curry, coalgebraHomAdjunction_counit]
  change H.X ◁ B.mon.mul ≫ MonoidalClosed.uncurry p = H.X ◁ (p ⊗ₘ p) ≫ _ ≫ _ ≫ B.mon.mul
  rw [hp, hb, ← Category.assoc (H.X ◁ (p ⊗ₘ p)), hn]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, he]
  simpa only [CategoryTheory.Functor.id_obj, Category.assoc] using congrArg (fun t => t ≫ B.mon.mul)
    (coalgebraTensorCounit_tensor R H B.X B.X).symm

/-- 概要：畳み込みの convolutionUnitMap を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
def convolutionUnitMap : B ⟶ (convolutionAlgebraFunctor R H).obj B :=
  Mon.Hom.mk' (convolutionUnitHom R H B)
    (convolutionUnitHom_one R H B) (convolutionUnitHom_mul R H B)


end SerrePositivity.EInfinity.DGAlgebra
