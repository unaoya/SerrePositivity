module

public import SerrePositivity.DifferentialGraded.Algebras.ConvolutionConstant
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ProjectivePullbackHomClosed

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


private lemma curryUnitComparison {C : Type v} [Category.{w} C] [MonoidalCategory C]
    [Closed (𝟙_ C)] (X : C) :
    MonoidalClosed.curry (A := 𝟙_ C) (λ_ X).hom =
      (MonoidalClosed.unitNatIso (C := C)).hom.app X := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_eq]
  have h := conjugateEquiv_counit (Adjunction.id (C := C))
    (ihom.adjunction (𝟙_ C)) (leftUnitorNatIso C).hom X
  change (𝟙_ C) ◁ (MonoidalClosed.unitNatIso (C := C)).hom.app X ≫
    (ihom.ev (𝟙_ C)).app X = (λ_ X).hom ≫ 𝟙 X at h
  simpa only [Category.comp_id] using h.symm

variable (R : Type u) [CommRing R]

/-- 概要：畳み込みの convolutionUnitHom_unit_pre を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma convolutionUnitHom_unit_pre (H : Comon (Complex R)) (B : Mon (Complex R)) :
    _root_.SerrePositivity.DGAlgebra.convolutionUnitHom R H B =
      (MonoidalClosed.unitNatIso (C := Complex R)).hom.app B.X ≫
        (MonoidalClosed.pre ε[H.X]).app B.X := by
  rw [_root_.SerrePositivity.DGAlgebra.convolutionUnitHom, _root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit_app,
    ← MonoidalClosed.curry_pre_app, _root_.SerrePositivity.DGAlgebra.curryUnitComparison]


end SerrePositivity.DGAlgebra
