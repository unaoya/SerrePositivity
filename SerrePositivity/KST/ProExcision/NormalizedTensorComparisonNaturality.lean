module
public import SerrePositivity.KST.ProExcision.NormalizedTensorComparison
public import SerrePositivity.KST.ProExcision.TensorHomotopyGeneralNaturality
public import SerrePositivity.KST.ProExcision.ChainHomotopySquareLinear

/-!
# 正規化テンソル比較の自然性

概要：標準 EZ 比較と因子内の全鎖比較から得るテンソル比較は自然。
方針：EZ、全テンソル、AW、shuffle の自然性を連結する。
規約：KST Construction A.5 の右辺の augmentation 補正。
使われ方：外部 G の作用と可換な実区間ホモトピーの構成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex AlgebraicTopology
variable {C C' D D' E E' F F' : SimplicialObject (ModuleCat.{u} ℤ)}

/-- 概要：単体的テンソル写像は二因子の合成を保つ。
方針：各次数のテンソル写像の合成則を使う。
規約：KST A.5。使われ方：四辺の可換な正方形のテンソル化。 -/
lemma simplicialIntegerTensorMap_comp (a : C ⟶ C') (b : D ⟶ D')
    (f : C' ⟶ E) (g : D' ⟶ F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (a ≫ f) (b ≫ g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap a b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap f g := by
  apply NatTrans.ext
  funext n
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp (a.app n) (f.app n) (b.app n) (g.app n)

/-- 概要：標準テンソル比較は四辺の可換な正方形を保つ。
方針：EZ の自然性を後合成し、端点の等式による比較を付ける。
規約：KST A.5。使われ方：厳密化を含む全比較の前半。 -/
lemma normalizedTensorComparisonHomotopy_square
    (f : C ⟶ E) (g : D ⟶ F) (f' : C' ⟶ E') (g' : D' ⟶ F')
    (a : C ⟶ C') (b : D ⟶ D') (c : E ⟶ E') (d : F ⟶ F')
    (hf : a ≫ f' = f ≫ c) (hg : b ≫ g' = g ≫ d) :
    ChainHomotopySquare
      ((normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap a b))
      ((normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap c d))
      (normalizedTensorComparisonHomotopy f g) (normalizedTensorComparisonHomotopy f' g') := by
  dsimp only [normalizedTensorComparisonHomotopy]
  apply ChainHomotopySquare.trans (ChainHomotopySquare.ofEq _ _ _ _)
  apply ChainHomotopySquare.trans
  · apply ChainHomotopySquare.compRight (normalizedEZHomotopy_square a b)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← simplicialIntegerTensorMap_comp, ← simplicialIntegerTensorMap_comp, hf, hg]
  · apply ChainHomotopySquare.ofEq

/-- 概要：因子内の全鎖比較を挟む正規化テンソル比較も自然。
方針：全テンソルの自然性を AW と shuffle で挟み、標準比較と連結する。
規約：KST A.5、比較の自然性を入力の自然性から導く。
使われ方：augmentation 補正式の左辺と各右辺の比較。 -/
lemma normalizedTensorComparisonWithHomotopies_square
    (f : C ⟶ E) (g : D ⟶ F) (f' : C' ⟶ E') (g' : D' ⟶ F')
    {U : (normalizedMooreComplex _).obj C ⟶ (normalizedMooreComplex _).obj E}
    {V : (normalizedMooreComplex _).obj D ⟶ (normalizedMooreComplex _).obj F}
    {U' : (normalizedMooreComplex _).obj C' ⟶ (normalizedMooreComplex _).obj E'}
    {V' : (normalizedMooreComplex _).obj D' ⟶ (normalizedMooreComplex _).obj F'}
    (h : Homotopy ((normalizedMooreComplex _).map f) U)
    (k : Homotopy ((normalizedMooreComplex _).map g) V)
    (h' : Homotopy ((normalizedMooreComplex _).map f') U')
    (k' : Homotopy ((normalizedMooreComplex _).map g') V')
    (a : C ⟶ C') (b : D ⟶ D') (c : E ⟶ E') (d : F ⟶ F')
    (hf : a ≫ f' = f ≫ c) (hg : b ≫ g' = g ≫ d)
    (hU : (normalizedMooreComplex _).map a ≫ U' = U ≫ (normalizedMooreComplex _).map c)
    (hh : ChainHomotopySquare ((normalizedMooreComplex _).map a) ((normalizedMooreComplex _).map c) h h')
    (hk : ChainHomotopySquare ((normalizedMooreComplex _).map b) ((normalizedMooreComplex _).map d) k k') :
    ChainHomotopySquare
      ((normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap a b))
      ((normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap c d))
      (normalizedTensorComparisonWithHomotopies f g h k)
      (normalizedTensorComparisonWithHomotopies f' g' h' k') := by
  dsimp only [normalizedTensorComparisonWithHomotopies]
  apply ChainHomotopySquare.trans (normalizedTensorComparisonHomotopy_square f g f' g' a b c d hf hg)
  apply ChainHomotopySquare.trans (ChainHomotopySquare.ofEq _ _ _ _)
  apply ChainHomotopySquare.trans
  · apply ChainHomotopySquare.compRight
    · apply ChainHomotopySquare.compLeft
      · have hgn := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) hg
        simp only [CategoryTheory.Functor.map_comp] at hgn
        exact chainIntegerTensorHomotopy_naturality h h' k k'
          ((normalizedMooreComplex _).map a) ((normalizedMooreComplex _).map b)
          ((normalizedMooreComplex _).map c) ((normalizedMooreComplex _).map d) hU hgn hh hk
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney_naturality a b
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle_naturality c d
  · apply ChainHomotopySquare.ofEq

/-- 概要：augmentation 補正した三項の鎖比較は自然。
方針：二つの因子の比較と第三項の標準比較を加減する。
規約：KST A.5 の右辺の augmentation 補正 f⊗e′+e⊗g−e⊗e′。
使われ方：低次消滅した全テンソルとの比較の同変性。 -/
lemma normalizedTensorAugmentationComparison_square
    (f e : C ⟶ E) (g e' : D ⟶ F)
    (f₁ e₁ : C' ⟶ E') (g₁ e₁' : D' ⟶ F')
    {U : (normalizedMooreComplex _).obj C ⟶ (normalizedMooreComplex _).obj E}
    {V : (normalizedMooreComplex _).obj D ⟶ (normalizedMooreComplex _).obj F}
    {U₁ : (normalizedMooreComplex _).obj C' ⟶ (normalizedMooreComplex _).obj E'}
    {V₁ : (normalizedMooreComplex _).obj D' ⟶ (normalizedMooreComplex _).obj F'}
    (h : Homotopy ((normalizedMooreComplex _).map f) U)
    (k : Homotopy ((normalizedMooreComplex _).map g) V)
    (h₁ : Homotopy ((normalizedMooreComplex _).map f₁) U₁)
    (k₁ : Homotopy ((normalizedMooreComplex _).map g₁) V₁)
    (a : C ⟶ C') (b : D ⟶ D') (c : E ⟶ E') (d : F ⟶ F')
    (hf : a ≫ f₁ = f ≫ c) (hg : b ≫ g₁ = g ≫ d)
    (he : a ≫ e₁ = e ≫ c) (he' : b ≫ e₁' = e' ≫ d)
    (hU : (normalizedMooreComplex _).map a ≫ U₁ = U ≫ (normalizedMooreComplex _).map c)
    (hh : ChainHomotopySquare ((normalizedMooreComplex _).map a) ((normalizedMooreComplex _).map c) h h₁)
    (hk : ChainHomotopySquare ((normalizedMooreComplex _).map b) ((normalizedMooreComplex _).map d) k k₁) :
    ChainHomotopySquare
      ((normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap a b))
      ((normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap c d))
      (normalizedTensorAugmentationComparison f e g e' h k)
      (normalizedTensorAugmentationComparison f₁ e₁ g₁ e₁' h₁ k₁) := by
  dsimp only [normalizedTensorAugmentationComparison]
  apply ChainHomotopySquare.trans (ChainHomotopySquare.ofEq _ _ _ _)
  apply ChainHomotopySquare.trans
  · apply ChainHomotopySquare.add
    · apply ChainHomotopySquare.add
      · exact normalizedTensorComparisonWithHomotopies_square f e' f₁ e₁' h _ h₁ _
          a b c d hf he' hU hh (ChainHomotopySquare.refl _ _ _ _)
      · have hen := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) he
        simp only [CategoryTheory.Functor.map_comp] at hen
        exact normalizedTensorComparisonWithHomotopies_square e g e₁ g₁ _ k _ k₁
          a b c d he hg hen (ChainHomotopySquare.refl _ _ _ _) hk
    · exact (normalizedTensorComparisonHomotopy_square e e' e₁ e₁' a b c d he he').smul (-1 : ℤ)
  · apply ChainHomotopySquare.ofEq

end SerrePositivity.KST.ProExcision
