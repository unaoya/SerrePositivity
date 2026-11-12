module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.StrictTransportUnderEdge
public import SerrePositivity.KST.Fibration.SectionEdgePrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianStrictTransport
public import SerrePositivity.KST.LocalizingInvariants.IntervalPostcompositionFamily

/-! # strict transport の元の undercategory 内の恒等射からの辺 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 始点は元の恒等射の頂点。 -/
theorem strictTransportUnderEdge_zero {I : Type u} [Category.{u} I] {c d : I} (f : c ⟶ d) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge f).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 c)) := by
  rw [← intervalMap_source, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge, Equiv.apply_symm_apply]
  exact ComposableArrows.ext₀ rfl

/-- 終点は元の入力射の under 頂点。 -/
theorem strictTransportUnderEdge_one {I : Type u} [Category.{u} I] {c d : I} (f : c ⟶ d) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge f).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk f) := by
  rw [← intervalMap_target, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge, Equiv.apply_symm_apply]
  exact ComposableArrows.ext₀ rfl

end SerrePositivity.KST.Fibration
