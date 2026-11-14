module
public import SerrePositivity.KST.SConstruction.StableZeroSquareAlignedTriangle
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutHomotopy

/-!
概要：元零四角形全体の比較を、元上下二胞体の全比較を保って構成する。
方針：共有対角だけを同じ類で整列し、元二三角形の pushout で貼る。
規約：元両四角形と上下全比較の類を保持。使われ方：実右面の全図式比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories LocalizingInvariants
open scoped Simplicial
variable {f g : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}}
  (H : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare f) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare g))
  (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex f 0 1)))

/-- 概要：元上比較と同じ全対角を持つ元下二胞体比較の実代表。
方針：同じ元全比較の類と元二胞体を保つ存在証明から選ぶ。
規約：全下比較の類を保持。使われ方：元四角形の貼り合わせ。 -/
def squareFrameAlignedLowerTriangleHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ g) :=
  (exists_squareFrameAlignedLowerTriangle H hz).choose

/-- 概要：同じ元下比較代表の対角は元上比較の対角に厳密に一致する。
方針：元存在証明の対角回収式を使う。
規約：全時刻・全単体の等号。使われ方：全二三角形の接合。 -/
lemma squareFrameAlignedLowerTriangleHomotopy_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (squareFrameAlignedLowerTriangleHomotopy H hz).h =
      (squareFrameTriangleDiagonalHomotopy H 0).h :=
  (exists_squareFrameAlignedLowerTriangle H hz).choose_spec.1

/-- 概要：同じ元下比較代表は元全下比較の射の類を保持する。
方針：元存在証明の全類回収式を使う。
規約：元全二胞体比較。使われ方：指定短辺比較と可逆性の保持。 -/
lemma squareFrameAlignedLowerTriangleHomotopy_class :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (squareFrameAlignedLowerTriangleHomotopy H hz)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (squareFrameTriangleHomotopy H 1)) :=
  (exists_squareFrameAlignedLowerTriangle H hz).choose_spec.2

/-- 概要：同じ元上下全比較は同じ共有対角で厳密に接合できる。
方針：元下代表の対角指定を使う。
規約：元両二胞体を保持。使われ方：元全四角形の比較。 -/
lemma stableZeroSquareHomotopy_gluing :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (squareFrameTriangleHomotopy H 0).h =
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (squareFrameAlignedLowerTriangleHomotopy H hz).h :=
  (squareFrameAlignedLowerTriangleHomotopy_diagonal H hz).symm

/-- 概要：元零四角形の全単体を元四境界比較で結ぶ実ホモトピー。
方針：元上下二胞体を共有対角に沿って貼る。
規約：元両面と上下比較の類を保持。使われ方：元全四角形比較。 -/
def stableZeroSquareHomotopy : SSet.Homotopy f g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout (squareFrameTriangleHomotopy H 0)
    (squareFrameAlignedLowerTriangleHomotopy H hz) (stableZeroSquareHomotopy_gluing H hz)

/-- 概要：元全四角形比較の上面は元上二胞体比較そのもの。
方針：元 pushout の左包含を回収する。
規約：全単体の等号。使われ方：元零側面と上二胞体の保持。 -/
lemma stableZeroSquareHomotopy_upper :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ (Δ[1] : SSet.{u + 1})) ≫ (stableZeroSquareHomotopy H hz).h =
      (squareFrameTriangleHomotopy H 0).h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy_inl _ _ _ _

/-- 概要：元全四角形比較の下面は元下全比較の類を保つ実代表。
方針：元 pushout の右包含を回収する。
規約：全単体の等号。使われ方：元包含・商辺と下二胞体の保持。 -/
lemma stableZeroSquareHomotopy_lower :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ (Δ[1] : SSet.{u + 1})) ≫ (stableZeroSquareHomotopy H hz).h =
      (squareFrameAlignedLowerTriangleHomotopy H hz).h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy_inr _ _ _ _

/-- 概要：同じ元下比較代表は元全比較の類の保持により可逆。
方針：元射の類の等号で可逆性を回収する。
規約：元下代表を保持。使われ方：全四角形比較の可逆性。 -/
lemma squareFrameAlignedLowerTriangleHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (squareFrameAlignedLowerTriangleHomotopy H hz)) := by
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy _))
  rw [squareFrameAlignedLowerTriangleHomotopy_class]
  exact squareFrameTriangleHomotopy_isInvertible H 1

/-- 概要：元両四角形全体を結ぶ同じ実比較は可逆。
方針：元上下二胞体の全比較の点ごとの可逆性を pushout 上で検出する。
規約：元全比較を保持。使われ方：全図式の同型。 -/
lemma stableZeroSquareHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (stableZeroSquareHomotopy H hz)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy_isInvertible _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout (stableZeroSquareHomotopy H hz)
    (squareFrameTriangleHomotopy H 0) (squareFrameAlignedLowerTriangleHomotopy H hz)
    (stableZeroSquareHomotopy_upper H hz) (stableZeroSquareHomotopy_lower H hz)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge _ (squareFrameTriangleHomotopy_isInvertible H 0))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge _
      (squareFrameAlignedLowerTriangleHomotopy_isInvertible H hz))

/-- 概要：元零四角形全体を指定元境界で比較する全関手同型。
方針：同じ元全ホモトピーの可逆な辺の類を使う。
規約：元全四角形・元二胞体を保持。使われ方：実右面の全図式比較。 -/
def stableZeroSquareComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g :=
  @asIso _ _ _ _ (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (stableZeroSquareHomotopy H hz)))
    (stableZeroSquareHomotopy_isInvertible H hz)
end SerrePositivity.KST.SConstruction
