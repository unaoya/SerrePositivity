module
public import SerrePositivity.KST.SConstruction.StableZeroSquareTriangleClass
public import SerrePositivity.KST.SConstruction.SpecifiedTriangleDiagonalRepresentative
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom

/-!
概要：元零四角形の下二胞体全比較を、元上比較と厳密に同じ対角へ合わせる。
方針：元二比較の対角の類を照合し、同じ全比較の類を保つ代表修正を使う。
規約：元四角形・両二単体・元下比較の類を保持。使われ方：全右面比較の貼り合わせ。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories LocalizingInvariants
open scoped Simplicial
variable {f g : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}}
  (H : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare f) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare g))

private lemma lowerDiagonalMapEq (p : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) :
    stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ p := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal]

/-- 概要：元下二胞体の対角へ、元上比較の全対角ホモトピーを置く。
方針：共有面の元等号で端点の表示だけを合わせる。
規約：元上比較の全写像を保持。使われ方：元下比較への指定対角代表。 -/
def squareFrameLowerAlignedDiagonalHomotopy : SSet.Homotopy
    (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ f)
    (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ g) where
  h := (squareFrameTriangleDiagonalHomotopy H 0).h
  h₀ := (squareFrameTriangleDiagonalHomotopy H 0).h₀.trans (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal]; rfl)
  h₁ := (squareFrameTriangleDiagonalHomotopy H 0).h₁.trans (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal]; rfl)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：元下二胞体の対角制限は指定した元上対角代表と同じ類。
方針：同じ零対角上の一意性を元端点等号で輸送する。
規約：元両二胞体と全下比較の類を保持。使われ方：同じ類を保つ代表修正。 -/
lemma squareFrameLowerAlignedDiagonalHomotopy_class
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex f 0 1))) :
    SSet.Truncated.HomotopyCategory.homMk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (squareFrameTriangleHomotopy H 1)).map
          ((truncation 2).map ((pre (stdSimplex.δ (1 : Fin 3))).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}))) =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (squareFrameLowerAlignedDiagonalHomotopy H)) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (squareFrameTriangleHomotopy H 1)).map
    ((truncation 2).map ((pre (stdSimplex.δ (1 : Fin 3))).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}))
  have hx := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (lowerDiagonalMapEq f)
  have hy := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (lowerDiagonalMapEq g)
  have he : e.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (squareFrameTriangleDiagonalHomotopy H 1)).edge := by
    change ((pre (stdSimplex.δ (1 : Fin 3))).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}).app
      (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry (squareFrameTriangleHomotopy H 1).h)) = _
    rw [← SSet.yonedaEquiv_comp]
    change SSet.yonedaEquiv (curry (squareFrameTriangleHomotopy H 1).h ≫
      (pre (stdSimplex.δ (1 : Fin 3))).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) = _
    rw [curry_pre_app]
    rfl
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport hx hy e
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (squareFrameTriangleDiagonalHomotopy H 1)) he
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport hx hy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (squareFrameLowerAlignedDiagonalHomotopy H))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (squareFrameTriangleDiagonalHomotopy H 0)) rfl
  apply (cancel_epi (eqToHom (congrArg SSet.HomotopyCategory.mk hx).symm)).1
  apply (cancel_mono (eqToHom (congrArg SSet.HomotopyCategory.mk hy))).1
  exact (Category.assoc _ _ _).trans ((hl.trans
    ((squareFrameTriangleDiagonalHomotopy_homMk_eq_of_zero H hz).symm.trans hu.symm)).trans
      (Category.assoc _ _ _).symm)

/-- 概要：元下全比較の類を保つ実ホモトピーは元上比較と対角全体を共有できる。
方針：元の対角制限を同じ類の指定代表へ厳密に修正する。
規約：元両二単体・元下全比較の類を同時保持。使われ方：元全四角形比較。 -/
lemma exists_squareFrameAlignedLowerTriangle
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex f 0 1))) :
    ∃ J : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ g),
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ J.h =
          (squareFrameTriangleDiagonalHomotopy H 0).h ∧
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J) =
          SSet.Truncated.HomotopyCategory.homMk
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (squareFrameTriangleHomotopy H 1)) :=
  exists_specifiedTriangleDiagonalRepresentative (squareFrameTriangleHomotopy H 1)
    (squareFrameLowerAlignedDiagonalHomotopy H) (squareFrameLowerAlignedDiagonalHomotopy_class H hz)
end SerrePositivity.KST.SConstruction
