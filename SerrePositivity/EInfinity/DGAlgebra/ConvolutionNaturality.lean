module

public import SerrePositivity.EInfinity.DGAlgebra.ConvolutionConstant
public import SerrePositivity.EInfinity.DGAlgebra.ConvolutionRestriction

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

variable (R : Type u) [CommRing R]

/-- 概要：畳み込みの convolutionUnitMap_precompose を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma convolutionUnitMap_precompose {H K : Comon (Complex R)} (f : H ⟶ K)
    (B : Mon (Complex R)) :
    convolutionUnitMap R K B ≫ convolutionRestriction R f B =
      convolutionUnitMap R H B := by
  apply Mon.Hom.ext'
  change MonoidalClosed.curry (A := K.X) ((coalgebraTensorCounit R K).app B.X) ≫
      (MonoidalClosed.pre f.hom).app B.X =
      MonoidalClosed.curry (A := H.X) ((coalgebraTensorCounit R H).app B.X)
  simp only [coalgebraTensorCounit_app]
  calc
    _ = MonoidalClosed.curry (A := H.X)
        (f.hom ▷ B.X ≫ (ε[K.X] ▷ B.X ≫ (λ_ B.X).hom)) :=
      MonoidalClosed.curry_pre_app f.hom (ε[K.X] ▷ B.X ≫ (λ_ B.X).hom)
    _ = _ := by
      congr 1
      rw [← comp_whiskerRight_assoc, IsComonHom.hom_counit]


/-- 概要：畳み込みの convolutionUnitMap_naturality を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma convolutionUnitMap_naturality (H : Comon (Complex R))
    {B C : Mon (Complex R)} (g : B ⟶ C) :
    convolutionUnitMap R H B ≫ (convolutionAlgebraFunctor R H).map g =
      g ≫ convolutionUnitMap R H C := by
  apply Mon.Hom.ext'
  change MonoidalClosed.curry (A := H.X) ((coalgebraTensorCounit R H).app B.X) ≫
      (ihom H.X).map g.hom = g.hom ≫
      MonoidalClosed.curry (A := H.X) ((coalgebraTensorCounit R H).app C.X)
  rw [← MonoidalClosed.curry_natural_right, ← MonoidalClosed.curry_natural_left]
  congr 1
  exact
    ((coalgebraTensorCounit R H).naturality g.hom).symm


end SerrePositivity.EInfinity.DGAlgebra
