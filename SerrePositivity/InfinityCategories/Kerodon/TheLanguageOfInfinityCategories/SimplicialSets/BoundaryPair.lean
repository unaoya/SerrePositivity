module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapes

/-! # 二頂点を指定する区間の境界図式

概要：二つの頂点を区間の境界上に貼り、実際の辺の境界と比較する。
方針：二端点の prism の図式に点の右単位同型を適用する。
規約：零端点は第一頂点、一端点は第二頂点。
使われ方：S4 の両端を指定した普遍余錐間の辺の持ち上げ。

対応節は Kerodon 1.1（Tag 0004）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets

/-- 概要：指定された二頂点から区間の境界図式を作る。
方針：点をパラメーターとした二端点の図式を使う。
規約：境界の端点の順は零、一。使われ方：辺の境界持ち上げ。 -/
def stableBoundaryPair {X : SSet.{u}} (x y : X _⦋0⦌) : (boundary 1 : SSet.{u}) ⟶ X :=
  (ρ_ (boundary 1 : SSet.{u})).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (SSet.const x) (SSet.const y)

/-- 概要：二頂点の境界図式の零端点は第一頂点。
方針：零端点で評価する。
規約：厳密な Yoneda 表示の等式。使われ方：持ち上げた辺の始点。 -/
lemma stableBoundaryPair_zero {X : SSet.{u}} (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex 0 0 ≫ stableBoundaryPair x y = SSet.yonedaEquiv.symm x := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change (if (0 : Fin 2) = 0 then _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0 else _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 0) = x
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  rfl

/-- 概要：二頂点の境界図式の一端点は第二頂点。
方針：一端点で評価する。
規約：厳密な Yoneda 表示。使われ方：持ち上げた辺の終点。 -/
lemma stableBoundaryPair_one {X : SSet.{u}} (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex 0 1 ≫ stableBoundaryPair x y = SSet.yonedaEquiv.symm y := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change (if (1 : Fin 2) = 0 then _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0 else _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 0) = y
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  exact ite_eq_right (by decide)

/-- 概要：区間の境界からの二つの射は二端点で一致すれば等しい。
方針：境界の全単体がいずれかの頂点の定値単体であることを使う。
規約：値域は任意。使われ方：辺の境界の可換性。 -/
lemma stableBoundaryPair_hom_ext {X : SSet.{u}} {f g : (boundary 1 : SSet.{u}) ⟶ X}
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex 0 0 ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex 0 0 ≫ g)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex 0 1 ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex 0 1 ≫ g) : f = g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  have hs : ∃ i : Fin 2, s = (boundary 1 : SSet.{u}).map
      (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex 0 i)) := by
    refine ⟨s.val 0, ?_⟩
    apply Subtype.ext
    apply stdSimplex.ext
    intro j
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.boundaryOne_simplex_constant s j
  obtain ⟨i, rfl⟩ := hs
  have hv : f.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex 0 i)) =
      g.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex 0 i)) := by
    have h := congrArg SSet.yonedaEquiv (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex 0 i ≫ f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex 0 i ≫ g from by fin_cases i <;> assumption)
    simpa only [SSet.yonedaEquiv_comp] using h
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hv]

/-- 概要：二頂点の境界図式は値域の射と可換。
方針：二端点で比較する。
規約：射に追加仮定なし。使われ方：持ち上げ四角形の可換性。 -/
lemma stableBoundaryPair_postcomp {X Y : SSet.{u}} (x y : X _⦋0⦌) (p : X ⟶ Y) :
    stableBoundaryPair x y ≫ p = stableBoundaryPair (p.app (Opposite.op ⦋0⦌) x)
      (p.app (Opposite.op ⦋0⦌) y) := by
  apply stableBoundaryPair_hom_ext
  · rw [← Category.assoc, stableBoundaryPair_zero, stableBoundaryPair_zero,
      SSet.yonedaEquiv_symm_comp]
  · rw [← Category.assoc, stableBoundaryPair_one, stableBoundaryPair_one,
      SSet.yonedaEquiv_symm_comp]

/-- 概要：辺の両端の境界図式はその辺の境界制限に一致する。
方針：二端点の条件を Yoneda で読む。
規約：二切断の実際の辺。使われ方：辺の持ち上げ。 -/
lemma stableBoundaryPair_edge {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    stableBoundaryPair x y = (boundary 1).ι ≫ SSet.yonedaEquiv.symm e.edge := by
  apply stableBoundaryPair_hom_ext
  · rw [stableBoundaryPair_zero, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι]
    have hv : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
      apply SSet.yonedaEquiv.injective
      decide
    rw [hv]
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source e).symm
  · rw [stableBoundaryPair_one, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι]
    have hv : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
      apply SSet.yonedaEquiv.injective
      decide
    rw [hv]
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target e).symm

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
