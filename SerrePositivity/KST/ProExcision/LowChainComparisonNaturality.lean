module
public import SerrePositivity.KST.ProExcision.LowChainComparisonReconstruction
public import SerrePositivity.KST.ProExcision.ChainHomotopyCylinderNaturality
public import SerrePositivity.KST.ProExcision.ChainHomotopySquareLinear

/-!
# 低次の鎖比較からの実区間復元の自然性

概要：二つの鎖比較の自然性から、それらの差で復元した実区間射の自然性を導く。
方針：差のホモトピーの自然性、正規化の忠実性、実区間復元の自然性を合成する。
規約：KST Construction A.5 の右辺の augmentation 補正を保つ。
使われ方：因子内の同変な入力から構成した補正式を外部 G の作用に移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex AlgebraicTopology
open scoped Simplicial
variable {X X' : SSet.{u}} {D D' : SimplicialObject (ModuleCat.{u} ℤ)}
variable {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ D} {f' g' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X' ⟶ D'}
variable {R S : (normalizedMooreComplex _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) ⟶ (normalizedMooreComplex _).obj D}
variable {R' S' : (normalizedMooreComplex _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X') ⟶ (normalizedMooreComplex _).obj D'}

/-- 概要：二つの自然な鎖比較の差によるホモトピーは自然。
方針：和、負の整数倍、恒等比較、等式による端点同定に分解する。
規約：KST A.5、補正終点 R−S+N(g)。
使われ方：低次の比較からの区間復元の同変性。 -/
lemma chainComparisonDifferenceHomotopy_square
    {H₁ : Homotopy ((normalizedMooreComplex _).map f) R}
    {H₂ : Homotopy ((normalizedMooreComplex _).map g) S}
    {H₁' : Homotopy ((normalizedMooreComplex _).map f') R'}
    {H₂' : Homotopy ((normalizedMooreComplex _).map g') S'}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X') (b : D ⟶ D')
    (h₁ : ChainHomotopySquare ((normalizedMooreComplex _).map a)
      ((normalizedMooreComplex _).map b) H₁ H₁')
    (h₂ : ChainHomotopySquare ((normalizedMooreComplex _).map a)
      ((normalizedMooreComplex _).map b) H₂ H₂') :
    ChainHomotopySquare ((normalizedMooreComplex _).map a)
      ((normalizedMooreComplex _).map b)
      (chainComparisonDifferenceHomotopy H₁ H₂) (chainComparisonDifferenceHomotopy H₁' H₂') := by
  dsimp only [chainComparisonDifferenceHomotopy]
  apply ChainHomotopySquare.trans (ChainHomotopySquare.ofEq _ _ _ _)
  apply ChainHomotopySquare.trans
  · exact (h₁.add (h₂.smul (-1 : ℤ))).add (ChainHomotopySquare.refl _ _ _ _)
  · apply ChainHomotopySquare.ofEq

/-- 概要：低次一致する鎖比較から復元した実区間射は自然。
方針：補正終点の自然性を正規化の忠実性で戻し、差のホモトピーを復元する。
規約：KST A.5、同変性を結論の仮定にしない。
使われ方：augmentation 補正式の実 m 次ホモトピーの外部作用への移送。 -/
lemma linearizedMHomotopyOfChainComparisons_naturality
    (H₁ : Homotopy ((normalizedMooreComplex _).map f) R)
    (H₂ : Homotopy ((normalizedMooreComplex _).map g) S)
    (H₁' : Homotopy ((normalizedMooreComplex _).map f') R')
    (H₂' : Homotopy ((normalizedMooreComplex _).map g') S')
    (m : ℕ) (hRS : ∀ n, n ≤ m → R.f n = S.f n)
    (m' : ℕ) (hRS' : ∀ n, n ≤ m' → R'.f n = S'.f n)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X') (b : D ⟶ D')
    (hf : a ≫ f' = f ≫ b) (hg : a ≫ g' = g ≫ b)
    (hR : (normalizedMooreComplex _).map a ≫ R' = R ≫ (normalizedMooreComplex _).map b)
    (hS : (normalizedMooreComplex _).map a ≫ S' = S ≫ (normalizedMooreComplex _).map b)
    (h₁ : ChainHomotopySquare ((normalizedMooreComplex _).map a)
      ((normalizedMooreComplex _).map b) H₁ H₁')
    (h₂ : ChainHomotopySquare ((normalizedMooreComplex _).map a)
      ((normalizedMooreComplex _).map b) H₂ H₂') :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap a (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder X') ≫
      (linearizedMHomotopyOfChainComparisons (X := X') (D := D') (f := f') (g := g') H₁' H₂' m' hRS').h =
        (linearizedMHomotopyOfChainComparisons (X := X) (D := D) (f := f) (g := g) H₁ H₂ m hRS).h ≫ b := by
  let e := normalizedMapReconstruct (R - S + (normalizedMooreComplex _).map g)
  let e' := normalizedMapReconstruct (R' - S' + (normalizedMooreComplex _).map g')
  have he : a ≫ e' = e ≫ b := by
    apply normalizedMap_eq_of_map_eq
    simp only [CategoryTheory.Functor.map_comp, e, e', normalizedMapReconstruct_map,
      Preadditive.comp_add, Preadditive.comp_sub, Preadditive.add_comp, Preadditive.sub_comp]
    have hgn := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) hg
    simp only [CategoryTheory.Functor.map_comp] at hgn
    rw [hR, hS, hgn]
  apply chainHomotopyCylinderReconstruct_naturality _ _ a b hf he
  apply ChainHomotopySquare.trans
  · exact chainComparisonDifferenceHomotopy_square a b h₁ h₂
  · apply ChainHomotopySquare.ofEq

end SerrePositivity.KST.ProExcision
