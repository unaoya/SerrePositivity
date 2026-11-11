module
public import SerrePositivity.KST.Fibration.VerdierNullHomFamilies
public import SerrePositivity.KST.Fibration.VerdierLowerCompositeMap
public import SerrePositivity.KST.Fibration.ExactMapCoordinates

/-! # 元の共有対角の座標における合成頂点と、指定包含・商の同じ実合成 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 対角の対象座標だけを輸送しても、元の二胞体の同じ合成完全射を保持する。 -/
theorem stableTriangleHomOverDiagonal_composite_heq (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 s = a) :
    HEq (stableHomExactMap ((stableTriangleHomOverDiagonal a s h).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentTriangleFullPath))) (stableTriangleCompositeMap s) := by
  subst a
  rfl

/-- 元の上下二胞体族の同じ合成 path の実頂点。 -/
def verdierNullCompositeVertex (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    (((verdierNullDiagonal d).obj ⟨ULift.up 0⟩ ⟶[SSet.{u}]
      (verdierNullDiagonal d).obj ⟨ULift.up 1⟩)) _⦋0⦌ :=
  (verdierNullHomFamily d j).app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ coherentTriangleFullPath)

/-- 同じ合成頂点が表す元の完全射。対象座標は元の共有対角の両端。 -/
def verdierNullCompositeMap (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
      ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩) :=
  stableHomExactMap (verdierNullCompositeVertex d j)

/-- 下側の同じ合成頂点は、元の指定包含・商の合成を異種等号で回収する。 -/
theorem verdierNullCompositeMap_lower_heq (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    HEq (verdierNullCompositeMap d 1)
      (show d.left ⟶ d.right from (show d.left ⟶ d.middle from d.inclusion) ≫
        (show d.middle ⟶ d.right from d.projection)) :=
  (stableTriangleHomOverDiagonal_composite_heq _ _ (verdierTriangle_diagonal d 1)).trans
    (verdierLowerTriangleCompositeMap_heq d)

/-- 元の共有対角の始域座標は、元の指定左安定圏そのもの。 -/
theorem verdierNullDiagonal_source (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) = d.left :=
  (verdierUpperTriangle_source d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.left_eq)

/-- 元の共有対角の標的座標は、元の指定右安定圏そのもの。 -/
theorem verdierNullDiagonal_target (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) = d.right :=
  (verdierUpperTriangle_target d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.right_eq)

/-- 元の指定両端へ対象座標だけを輸送した、同じ二胞体の合成完全射。 -/
def verdierNullCompositeOriginalMap (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap d.left d.right :=
  exactMapTransport (verdierNullDiagonal_source d) (verdierNullDiagonal_target d)
    (verdierNullCompositeMap d j)

/-- 元の指定両端で読むと、下側の同じ合成頂点は元の包含・商の合成そのもの。 -/
theorem verdierNullCompositeOriginalMap_lower (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    verdierNullCompositeOriginalMap d 1 =
      (show d.left ⟶ d.right from (show d.left ⟶ d.middle from d.inclusion) ≫
        (show d.middle ⟶ d.right from d.projection)) :=
  eq_of_heq ((exactMapTransport_heq _ _ _).trans (verdierNullCompositeMap_lower_heq d))

/-- 元の合成頂点が表す完全射は、同じ全頂点で零値条件を満たす。 -/
theorem verdierNullCompositeMap_zero (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    ∀ x, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((verdierNullCompositeMap d j).hom.app (Opposite.op ⦋0⦌) x) := by
  have hv := verdierNullHomFamily_zero d j (ComposableArrows.mk₀ coherentTriangleFullPath)
  have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (verdierNullCompositeMap d j).hom) :=
    stableHomAmbient_vertex (verdierNullCompositeVertex d j) ▸ hv
  intro x
  have h := isZeroVertex_evaluateFunctorAt hz x
  rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at h

/-- 元の指定両端へ輸送した後にも、同じ合成完全射は全頂点を零対象へ送る。 -/
theorem verdierNullCompositeOriginalMap_zero (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    ∀ x, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((verdierNullCompositeOriginalMap d j).hom.app (Opposite.op ⦋0⦌) x) :=
  exactMapTransport_zero _ _ _ (verdierNullCompositeMap_zero d j)

end SerrePositivity.KST.Fibration
