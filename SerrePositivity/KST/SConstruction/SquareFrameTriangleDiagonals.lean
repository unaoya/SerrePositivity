module
public import SerrePositivity.KST.SConstruction.SquareFrameTriangleComparisons

/-!
概要：元上下二胞体比較の共有対角制限と、その指定両端経路を回収する。
方針：元二三角形の同じ対角と、元二短辺の全制限式を使う。
規約：上下の全比較を変更しない。使われ方：零対角上の比較一意性への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories LocalizingInvariants
open scoped Simplicial
variable {X : SSet.{u}} [Quasicategory X]
  {f g : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
  (H : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare f) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare g))

/-- 概要：元上下比較を同じ元共有対角に制限した全ホモトピー。
方針：元全三角形比較を同じ対角面で制限する。
規約：元対角を選び直さない。使われ方：上下共有対角の比較。 -/
def squareFrameTriangleDiagonalHomotopy (j : Fin 2) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ g) where
  h := (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ (squareFrameTriangleHomotopy H j).h
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc,
      (squareFrameTriangleHomotopy H j).h₀, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc,
      (squareFrameTriangleHomotopy H j).h₁, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：元上下比較の共有対角制限も同じ実比較として可逆。
方針：同じ元全三角形比較を対角への前合成で写す。
規約：元対角ホモトピーを保持。使われ方：共有零対角の全関手同型。 -/
lemma squareFrameTriangleDiagonalHomotopy_isInvertible (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (squareFrameTriangleDiagonalHomotopy H j)) := by
  let p := (pre (stdSimplex.δ (1 : Fin 3))).app X
  have hi := (squareFrameTriangleHomotopy_isInvertible H j).map p
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (squareFrameTriangleDiagonalHomotopy H j)).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (squareFrameTriangleHomotopy H j)).map
        ((truncation 2).map p)).edge := by
    change SSet.yonedaEquiv (curry ((stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
      (squareFrameTriangleHomotopy H j).h)) =
        p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry (squareFrameTriangleHomotopy H j).h))
    rw [← SSet.yonedaEquiv_comp]
    change SSet.yonedaEquiv (curry _) =
      SSet.yonedaEquiv (curry (squareFrameTriangleHomotopy H j).h ≫
        (pre (stdSimplex.δ (1 : Fin 3))).app X)
    rw [curry_pre_app]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr hi

private lemma diagonalFirstVertex :
    (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ stdSimplex.δ (1 : Fin 3) =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

private lemma diagonalLastVertex :
    (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ stdSimplex.δ (1 : Fin 3) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：元共有対角比較の始点経路は元第一側面の始点経路。
方針：対角端点と元前辺端点の標準包含の等号を使う。
規約：全一単体の厳密等号。使われ方：上下比較の始点経路の照合。 -/
lemma squareFrameTriangleDiagonalHomotopy_source (j : Fin 2) :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
        (squareFrameTriangleDiagonalHomotopy H j).h =
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ (squareFrameTriangleFirst H j).h := by
  change (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [← Category.assoc, ← comp_whiskerRight, diagonalFirstVertex, comp_whiskerRight,
    Category.assoc, (squareFrameTriangleHomotopy_faces H j).1]

/-- 概要：元共有対角比較の終点経路は元第二側面の終点経路。
方針：対角端点と元後辺端点の標準包含の等号を使う。
規約：全一単体の厳密等号。使われ方：上下比較の終点経路の照合。 -/
lemma squareFrameTriangleDiagonalHomotopy_target (j : Fin 2) :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
        (squareFrameTriangleDiagonalHomotopy H j).h =
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ (squareFrameTriangleLast H j).h := by
  change (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [← Category.assoc, ← comp_whiskerRight, diagonalLastVertex, comp_whiskerRight,
    Category.assoc, (squareFrameTriangleHomotopy_faces H j).2]

/-- 概要：元上下共有対角比較の両端経路は元四境界の共有経路により等しい。
方針：元始点・終点回収と元左下・右上経路式を使う。
規約：対角全比較の等号はまだ主張しない。使われ方：零対角の全比較一意性。 -/
lemma squareFrameTriangleDiagonalHomotopy_endpoints :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
        (squareFrameTriangleDiagonalHomotopy H 0).h =
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
        (squareFrameTriangleDiagonalHomotopy H 1).h ∧
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
        (squareFrameTriangleDiagonalHomotopy H 0).h =
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
        (squareFrameTriangleDiagonalHomotopy H 1).h := by
  constructor
  · exact (squareFrameTriangleDiagonalHomotopy_source H 0).trans
      (H.lower_left.symm.trans (squareFrameTriangleDiagonalHomotopy_source H 1).symm)
  · exact (squareFrameTriangleDiagonalHomotopy_target H 0).trans
      (H.upper_right.trans (squareFrameTriangleDiagonalHomotopy_target H 1).symm)
end SerrePositivity.KST.SConstruction
