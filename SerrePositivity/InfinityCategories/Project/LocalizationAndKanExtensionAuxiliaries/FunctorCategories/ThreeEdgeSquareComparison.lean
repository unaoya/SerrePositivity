module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.RelativeFunctorHomotopyComposition
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SquareThreeEdges
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.CompositionSquareComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SquareNormalizationHomotopy

/-!
概要：指定合成三角形の正方形と、同じ三辺を持つ正方形を相対的に比較する。
方針：上側の三角形比較と正規化の逆を、三辺への制限の fiber 内で合成する。
規約：合成ホモトピー・三辺の固定条件・元の二経路との二単体を保持する。
使われ方：B1 の comma 比較の両合成を検証する正方形全体の変形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：三辺を固定し、二段階の元の変形を同じ二単体に持つ正方形比較。
方針：ホモトピーに相対条件と合成三角形を添える。
規約：右辺は固定せず、その変形を後で導来 fiber の path と照合する。
使われ方：coherence を保持する正方形全体の合成。 -/
structure ThreeEdgeSquareComparison {A X : SSet.{u}} [Quasicategory X]
    {U V W : A ⟶ X} {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀)
    (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d₁) where
  homotopy : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle T).diagram Q.diagram
  restriction : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h =
    fst _ (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ≫ Q.diagram
  triangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (T.squareRelativeHomotopy Q.upperTriangle)
    Q.normalizationHomotopy homotopy
  triangle_restriction : triangle.diagram ≫ (pre _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι).app ((ihom A).obj X) =
    SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ≫ Q.diagram))

/-- 概要：比較の相対条件を三辺部分図式への任意の射で制限する。
方針：相対条件を前合成し、時間円柱の第一射影の自然性を使う。
規約：三辺のそれぞれへの制限にも使える raw な等式。
使われ方：合成した正方形の各境界辺を固定することの検証。 -/
lemma ThreeEdgeSquareComparison.restriction_precomp
    {A X K : SSet.{u}} [Quasicategory X]
    {U V W : A ⟶ X} {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} {T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀}
    {Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d₁} (c : ThreeEdgeSquareComparison T Q)
    (e : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges) :
    ((e ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι) ▷ (Δ[1] : SSet.{u})) ≫ c.homotopy.h =
      fst K (Δ[1] : SSet.{u}) ≫ e ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ≫ Q.diagram := by
  rw [MonoidalCategory.comp_whiskerRight, Category.assoc, c.restriction,
    ← Category.assoc, whiskerRight_fst, Category.assoc]

/-- 概要：三辺を共有する指定三角形と正方形の間の相対比較を構成する。
方針：上側の相対比較と正規化を戻す変形を、三辺制限の fiber 内で合成する。
規約：三辺の条件を追加仮定せず、入力の辺の仕様から証明する。
使われ方：B1 の基準正方形から元の comma 正方形への合成経路。 -/
noncomputable def threeEdgeSquareComparison {A X : SSet.{u}} [Quasicategory X]
    {U V W : A ⟶ X} {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀)
    (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d₁) : ThreeEdgeSquareComparison T Q := by
  let Q₀ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle T
  let Q₁ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle Q.upperTriangle
  let L := T.squareRelativeHomotopy Q.upperTriangle
  let R := Q.normalizationHomotopy
  let a := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ≫ Q.diagram
  have hf : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ≫ Q₀.diagram = a := by
    apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges_restriction_eq
    · exact Q₀.bottom.trans Q.bottom.symm
    · exact Q₀.left.trans Q.left.symm
    · exact Q₀.top.trans Q.top.symm
  have hg : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ≫ Q₁.diagram = a := by
    apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges_restriction_eq
    · exact Q₁.bottom.trans Q.bottom.symm
    · exact Q₁.left.trans Q.left.symm
    · exact Q₁.top.trans Q.top.symm
  have hl : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ▷ (Δ[1] : SSet.{u})) ≫ L.h =
      fst _ (Δ[1] : SSet.{u}) ≫ a := by
    apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges_homotopy_restriction Q.diagram L.h
    · rw [Q.bottom, SSet.comp_const]
      exact T.squareRelativeHomotopy_bottom Q.upperTriangle
    · rw [Q.left]
      exact T.squareRelativeHomotopy_left Q.upperTriangle
    · rw [Q.top]
      exact T.squareRelativeHomotopy_top Q.upperTriangle
  have hr : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ▷ (Δ[1] : SSet.{u})) ≫ R.h =
      fst _ (Δ[1] : SSet.{u}) ≫ a := by
    apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges_homotopy_restriction Q.diagram R.h
    · rw [Q.bottom, SSet.comp_const]
      exact Q.normalizationHomotopy_bottom
    · rw [Q.left]
      exact Q.normalizationHomotopy_left
    · rw [Q.top]
      exact Q.normalizationHomotopy_top
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.relativeFunctorHomotopyComposite _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι a hf hg rfl L R hl hr,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.relativeFunctorHomotopyComposite_restriction _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι a hf hg rfl L R hl hr,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.relativeFunctorHomotopyCompositeTriangle _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι a hf hg rfl L R hl hr,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.relativeFunctorHomotopyCompositeTriangle_restriction _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι a hf hg rfl L R hl hr⟩

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
