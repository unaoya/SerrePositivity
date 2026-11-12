module
public import SerrePositivity.KST.SConstruction.SquareFrameTrianglePrisms
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyInvertibility

/-!
概要：元四境界比較から作った上下二単体比較の可逆性を証明する。
方針：元二短辺が三頂点を覆うことと、指定した側面経路の可逆性を使う。
規約：元二単体・元実ホモトピーを保持。共有対角の一致は別工程。
使われ方：実恒等右面の元二胞体を保つ二つの全関手同型。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma restrictionVertexInvertible {A B X : SSet.{u}} [Quasicategory X]
    {f g : B ⟶ X} {f' g' : A ⟶ X} (k : A ⟶ B)
    (H : SSet.Homotopy f g) (G : SSet.Homotopy f' g')
    (h : (k ▷ (Δ[1] : SSet.{u})) ≫ H.h = G.h) (x : A _⦋0⦌)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge G x).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (k.app _ x)).toTruncated := by
  let z : (A ⊗ Δ[1] : SSet.{u}) _⦋1⦌ :=
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
  have he := congrArg (fun q : A ⊗ Δ[1] ⟶ X => q.app (Opposite.op ⦋1⦌) z) h
  have hid : k.app (Opposite.op ⦋1⦌) (SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj B) (k.app _ x)).edge := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map k x 1
  change H.h.app (Opposite.op ⦋1⦌)
    (k.app (Opposite.op ⦋1⦌) (SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _ at he
  rw [hid] at he
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (k.app _ x)).toTruncated)
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge G x).toTruncated) he).mpr hi

variable {X : SSet.{u}} [Quasicategory X]
  {f g : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
  (H : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare f) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare g))

private lemma firstVertexInvertible (j : Fin 2) (x : (Δ[1] : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (squareFrameTriangleFirst H j) x).toTruncated := by
  fin_cases j
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (squareFrameTriangleFirst H 0) x).toTruncated)
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H.left x).toTruncated) rfl).mpr (H.left_invertible x)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (squareFrameTriangleFirst H 1) x).toTruncated)
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H.bottom x).toTruncated) rfl).mpr (H.bottom_invertible x)

private lemma lastVertexInvertible (j : Fin 2) (x : (Δ[1] : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (squareFrameTriangleLast H j) x).toTruncated := by
  fin_cases j
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (squareFrameTriangleLast H 0) x).toTruncated)
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H.top x).toTruncated) rfl).mpr (H.top_invertible x)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (squareFrameTriangleLast H 1) x).toTruncated)
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H.right x).toTruncated) rfl).mpr (H.right_invertible x)

/-- 概要：元の上下二胞体を保つ同じ比較ホモトピーは可逆。
方針：元二短辺の三頂点被覆と元側面経路の可逆性を使う。
規約：比較写像を選び直さない。使われ方：元二胞体の全関手同型。 -/
lemma squareFrameTriangleHomotopy_isInvertible (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (squareFrameTriangleHomotopy H j)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise
  intro x
  have cover : ∃ (i : Fin 3) (hi : i = 2 ∨ i = 0)
      (y : (Δ[1] : SSet.{u}) _⦋0⦌), (stdSimplex.δ i).app _ y = x := by
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
    fin_cases i
    · exact ⟨2, Or.inl rfl, stdSimplex.obj₀Equiv.symm 0, rfl⟩
    · exact ⟨2, Or.inl rfl, stdSimplex.obj₀Equiv.symm 1, rfl⟩
    · exact ⟨0, Or.inr rfl, stdSimplex.obj₀Equiv.symm 1, rfl⟩
  obtain ⟨i, hi, y, rfl⟩ := cover
  rcases hi with rfl | rfl
  · exact restrictionVertexInvertible (stdSimplex.δ (2 : Fin 3))
      (squareFrameTriangleHomotopy H j) (squareFrameTriangleFirst H j)
      (squareFrameTriangleHomotopy_faces H j).1 y (firstVertexInvertible H j y)
  · exact restrictionVertexInvertible (stdSimplex.δ (0 : Fin 3))
      (squareFrameTriangleHomotopy H j) (squareFrameTriangleLast H j)
      (squareFrameTriangleHomotopy_faces H j).2 y (lastVertexInvertible H j y)

/-- 概要：元上下二単体全体を結ぶ同じ実全関手同型。
方針：元比較ホモトピーの可逆な辺の類を使う。
規約：元二単体・指定二短辺を保持。使われ方：実右面の二胞体比較。 -/
def squareFrameTriangleComparison (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ g) :=
  @asIso _ _ _ _ (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (squareFrameTriangleHomotopy H j)))
    (squareFrameTriangleHomotopy_isInvertible H j)
end SerrePositivity.KST.SConstruction
