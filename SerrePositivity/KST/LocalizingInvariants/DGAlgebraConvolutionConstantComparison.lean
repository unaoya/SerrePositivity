module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionConstant
public import SerrePositivity.HomologicalAlgebra.Complexes.HomHomotopy

/-!
概要：畳み込みの定数射を単位内部 Hom と実前合成に照合する。
方針：閉構造の転置で余単位を二つの元の射へ分解する。
規約：D・E2 の前合成と鎖ホモトピーの正本を読み取り専用で使う。
使われ方：AW 単体の定数射の弱同値性と零単体の同型性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex
open scoped ComonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

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

lemma convolutionConstantHom_unit_pre (H : Comon (Complex R)) (B : Mon (Complex R)) :
    convolutionConstantHom R H B =
      (MonoidalClosed.unitNatIso (C := Complex R)).hom.app B.X ≫
        (MonoidalClosed.pre ε[H.X]).app B.X := by
  rw [convolutionConstantHom, convolutionTensorCounit_app,
    ← MonoidalClosed.curry_pre_app, curryUnitComparison]

lemma convolutionPre_eq_homPrecompose {P Q : Complex R} (f : P ⟶ Q) (T : Complex R) :
    (MonoidalClosed.pre f).app T = homPrecompose f T := by
  have h := tensorHomEquiv_naturality_domain f ((ihom.ev Q).app T)
  change MonoidalClosed.curry (A := P) (f ▷ _ ≫ (ihom.ev Q).app T) =
    MonoidalClosed.curry (A := Q) ((ihom.ev Q).app T) ≫ homPrecompose f T at h
  rw [← MonoidalClosed.curry_pre_app, ← MonoidalClosed.uncurry_id_eq_ev,
    MonoidalClosed.curry_uncurry, Category.id_comp, Category.id_comp] at h
  exact h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
