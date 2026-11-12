module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullDiagonalHomotopyClass
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EdgeRepresentativeLift
/-!
概要：元下三角形の対角に、元上全比較と同じ実対角ホモトピーを指定する。
方針：元二胞体の対角の厳密回収で端点を移し、同じ零 Hom の射の類を使う。
規約：元実／絶対両二胞体は保持する。
使われ方：元下全三角形比較の類を保つ代表修正。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
/-- 概要：元下二胞体の両対角辺に、元上全比較と同じ全ホモトピーを置く。
方針：同じ元共有対角の面回収で端点の表示だけを合わせる。
規約：元上比較の全射。使われ方：元下全比較への指定実対角代表。 -/
def dgOdotMilnorNuNullLowerAlignedDiagonalHomotopy : SSet.Homotopy
    (stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d 1))
    (stdSimplex.δ (1 : Fin 3) ≫
      SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h 1)) where
  h := (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h).h
  h₀ := (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h).h₀.trans
    (dgOdotMilnorNuNullPrismTriangle_diagonal_actual R d 1).symm
  h₁ := (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h).h₁.trans
    (dgOdotMilnorNuNullPrismTriangle_diagonal_absolute R d h 1).symm
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property
/-- 概要：元下全比較の対角制限は、指定された元上対角代表と同じ類。
方針：元二対角の実端点を輸送し、同じ実区間 Hom の一意性を回収する。
規約：元下三角形の二胞体と両短辺比較の類を変えない。
使われ方：前合成の inner fibration による辺の代表修正。 -/
lemma dgOdotMilnorNuNullLowerAlignedDiagonalHomotopy_class :
    SSet.Truncated.HomotopyCategory.homMk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuNullLowerTriangleHomotopy R d h)).map
          ((truncation 2).map ((pre (stdSimplex.δ (1 : Fin 3))).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}))) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgOdotMilnorNuNullLowerAlignedDiagonalHomotopy R d h)) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (dgOdotMilnorNuNullLowerTriangleHomotopy R d h)).map
      ((truncation 2).map ((pre (stdSimplex.δ (1 : Fin 3))).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}))
  have hx := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgOdotMilnorNuNullPrismTriangle_diagonal_actual R d 1)
  have hy := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgOdotMilnorNuNullPrismTriangle_diagonal_absolute R d h 1)
  have he : e.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgOdotMilnorNuNullLowerDiagonalHomotopy R d h)).edge := by
    change ((pre (stdSimplex.δ (1 : Fin 3))).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}).app
      (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry
        (dgOdotMilnorNuNullLowerTriangleHomotopy R d h).h)) = _
    rw [← SSet.yonedaEquiv_comp]
    change SSet.yonedaEquiv (curry
      (dgOdotMilnorNuNullLowerTriangleHomotopy R d h).h ≫
        (pre (stdSimplex.δ (1 : Fin 3))).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}) = _
    rw [curry_pre_app]
    rfl
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport hx hy e
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuNullLowerDiagonalHomotopy R d h)) he
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport hx hy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuNullLowerAlignedDiagonalHomotopy R d h))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h)) rfl
  apply (cancel_epi (eqToHom (congrArg SSet.HomotopyCategory.mk hx).symm)).1
  apply (cancel_mono (eqToHom (congrArg SSet.HomotopyCategory.mk hy))).1
  exact (Category.assoc _ _ _).trans ((hl.trans
    ((dgOdotMilnorNuNullDiagonalHomotopy_homMk_eq R d h).trans hu.symm)).trans
      (Category.assoc _ _ _).symm)
end SerrePositivity.KST.SConstruction
