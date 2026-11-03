module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.CoconeMappingSpace
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceTriangleFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.LocalEdgeRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.LocalObjects
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeRestrictionTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeFiberPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeSectionFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.EdgeCosliceIntervalMap

/-!
概要：元の辺への局所性を、始点表示を指定した coslice の前合成の同値性と照合する。
方針：全 Hom の比較のホモトピー可換性と同値の二対三則を使う。
規約：元の比較辺と余極限余錐を保持。使われ方：HTT 5.5.4.5(2) の余極限閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の辺への局所性は、指定した両始点表示の coslice の前合成の同値性と一致。 -/
lemma isLocalForHom_edge_iff_coslicePrecomposition {X : SSet.{u}} [Quasicategory X]
    (e : (Δ[1] : SSet.{u}) ⟶ X) (a b : (Δ[0] : SSet.{u}) ⟶ X)
    (ha : stdSimplex.δ (1 : Fin 2) ≫ e = a) (hb : stdSimplex.δ (0 : Fin 2) ≫ e = b)
    (z : X _⦋0⦌) :
    IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk (edgeCosliceEdge e)) z ↔
      IsQCatEquivalence (cosliceEdgeFiberPrecomposition e a b ha hb z) := by
  subst a
  subst b
  have hs := (cosliceEdgeSectionFiber_homotopyEquivalence e z).isQCatEquivalence
  have hf : cosliceEdgeSectionFiber e z ≫
      cosliceRestrictionFiberMap e (stdSimplex.δ (1 : Fin 2)) z =
      cosliceEdgeFiberPrecomposition e (stdSimplex.δ (1 : Fin 2) ≫ e)
        (stdSimplex.δ (0 : Fin 2) ≫ e) rfl rfl z := by
    simpa only [normalizedCoconeRestrictionFiber_eq, eqToHom_refl, Category.comp_id] using
      cosliceEdgeSectionFiber_source e (stdSimplex.δ (1 : Fin 2) ≫ e) rfl z
  rw [isLocalForHom_edge_iff_sourceRestriction]
  constructor
  · intro h
    have hc := hs.comp h
    rwa [hf] at hc
  · intro h
    apply hs.cancel_left
    rw [hf]
    exact h

end SerrePositivity.InfinityCategories.HomotopyLimits
