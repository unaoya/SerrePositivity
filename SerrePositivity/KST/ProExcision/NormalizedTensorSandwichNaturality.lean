module
public import SerrePositivity.KST.ProExcision.NormalizedTensorComparisonNaturality

/-!
# AW と shuffle で挟んだ全テンソルの自然性

概要：正規化した二因子の自然な写像を対角の自然な写像へ移す。
方針：AW の自然性、全テンソルの合成則、shuffle の自然性を順に使う。
規約：KST Construction A.5、augmentation 補正の三項にも別々に適用する。
使われ方：低次一致する比較先の外部作用との可換性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex AlgebraicTopology

/-- 概要：AW と shuffle で挟んだ全テンソル写像は自然。
方針：三つの可換な正方形を合成する。
規約：KST A.5、実鎖写像の等式。
使われ方：厳密化した全テンソルと補正した三項の自然性。 -/
lemma normalizedTensorSandwich_naturality
    {C C' D D' E E' F F' : SimplicialObject (ModuleCat.{u} ℤ)}
    (U : (normalizedMooreComplex _).obj C ⟶ (normalizedMooreComplex _).obj E)
    (V : (normalizedMooreComplex _).obj D ⟶ (normalizedMooreComplex _).obj F)
    (U' : (normalizedMooreComplex _).obj C' ⟶ (normalizedMooreComplex _).obj E')
    (V' : (normalizedMooreComplex _).obj D' ⟶ (normalizedMooreComplex _).obj F')
    (a : C ⟶ C') (b : D ⟶ D') (c : E ⟶ E') (d : F ⟶ F')
    (hU : (normalizedMooreComplex _).map a ≫ U' = U ≫ (normalizedMooreComplex _).map c)
    (hV : (normalizedMooreComplex _).map b ≫ V' = V ≫ (normalizedMooreComplex _).map d) :
    (normalizedMooreComplex _).map (simplicialIntegerTensorMap a b) ≫
      (normalizedAlexanderWhitney C' D' ≫ chainIntegerTensorMap U' V' ≫ normalizedShuffle E' F') =
    (normalizedAlexanderWhitney C D ≫ chainIntegerTensorMap U V ≫ normalizedShuffle E F) ≫
      (normalizedMooreComplex _).map (simplicialIntegerTensorMap c d) := by
  rw [← Category.assoc, normalizedAlexanderWhitney_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (chainIntegerTensorMap ((normalizedMooreComplex _).map a) _),
    ← chainIntegerTensorMap_comp, hU, hV, chainIntegerTensorMap_comp]
  simp only [Category.assoc]
  rw [normalizedShuffle_naturality]

end SerrePositivity.KST.ProExcision
