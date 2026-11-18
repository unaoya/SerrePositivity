module

public import SerrePositivity.DifferentialGraded.Algebras.ConvolutionConstant
public import SerrePositivity.DifferentialGraded.Algebras.ConvolutionRestriction

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
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped _root_.CategoryTheory.ComonObj _root_.CategoryTheory.MonObj
open _root_.SerrePositivity.DifferentialGraded
namespace SerrePositivity.DGAlgebra
attribute [local instance] _root_.SerrePositivity.DGAlgebra.coalgebraConstant_oplax _root_.SerrePositivity.DGAlgebra.coalgebraTensor_oplax _root_.SerrePositivity.DGAlgebra.coalgebraHomLax

variable (R : Type u) [CommRing R]

/-- 概要：畳み込みの convolutionUnitMap_precompose を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma convolutionUnitMap_precompose {H K : Comon (Complex R)} (f : H ⟶ K)
    (B : Mon (Complex R)) :
    _root_.SerrePositivity.DGAlgebra.convolutionUnitMap R K B ≫ _root_.SerrePositivity.DGAlgebra.convolutionRestriction R f B =
      _root_.SerrePositivity.DGAlgebra.convolutionUnitMap R H B := by
  apply Mon.Hom.ext'
  change MonoidalClosed.curry (A := K.X) ((_root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit R K).app B.X) ≫
      (MonoidalClosed.pre f.hom).app B.X =
      MonoidalClosed.curry (A := H.X) ((_root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit R H).app B.X)
  simp only [_root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit_app]
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
    _root_.SerrePositivity.DGAlgebra.convolutionUnitMap R H B ≫ (_root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor R H).map g =
      g ≫ _root_.SerrePositivity.DGAlgebra.convolutionUnitMap R H C := by
  apply Mon.Hom.ext'
  change MonoidalClosed.curry (A := H.X) ((_root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit R H).app B.X) ≫
      (ihom H.X).map g.hom = g.hom ≫
      MonoidalClosed.curry (A := H.X) ((_root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit R H).app C.X)
  rw [← MonoidalClosed.curry_natural_right, ← MonoidalClosed.curry_natural_left]
  congr 1
  exact
    ((_root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit R H).naturality g.hom).symm


end SerrePositivity.DGAlgebra
