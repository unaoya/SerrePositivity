module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFiber
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence

/-! # 屋根 replacement の係数頂点と細分輸送の実辺

概要：係数頂点を全空間へ含め、添字の任意の射による輸送を実辺として表示する。
方針：元の係数頂点に定値な区間と、指定一射の nerve 辺を組にする。
規約：係数の Kan 性は不要。使われ方：局所持ち上げから全空間の連結成分の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite SSet
open scoped _root_.Simplicial
variable {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})

/-- 指定係数頂点を、指定添字上の replacement の頂点へ含める。 -/
def roofReplacementVertex (c : C) (g : (F.obj c) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F c).app (op ⦋0⦌) g

/-- 添字の指定射による係数の輸送は、全空間の指定実辺を持つ。 -/
def roofReplacementTransportEdge {c d : C} (r : c ⟶ d) (g : (F.obj c) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F).Edge (roofReplacementVertex F c g)
      (roofReplacementVertex F d ((F.map r).app (op ⦋0⦌) g)) := by
  refine SSet.Edge.mk ⟨ComposableArrows.mk₁ r, SSet.const g⟩ ?_ ?_
  · refine Sigma.ext (ComposableArrows.ext₀ rfl) ?_
    apply heq_of_eq
    change stdSimplex.δ (1 : Fin 2) ≫ SSet.const g ≫ F.map (𝟙 c) =
      SSet.yonedaEquiv.symm g
    rw [F.map_id, Category.comp_id, SSet.comp_const, SSet.yonedaEquiv_symm_zero]
  · refine Sigma.ext (ComposableArrows.ext₀ rfl) ?_
    apply heq_of_eq
    change stdSimplex.δ (0 : Fin 2) ≫ SSet.const g ≫ F.map r =
      SSet.yonedaEquiv.symm ((F.map r).app (op ⦋0⦌) g)
    rw [SSet.const_comp, SSet.comp_const, SSet.yonedaEquiv_symm_zero]

/-- 指定細分で輸送した係数頂点は、元の頂点と全空間の同じ連結成分に入る。 -/
lemma roofReplacementTransport_piZero {c d : C} (r : c ⟶ d) (g : (F.obj c) _⦋0⦌) :
    SSet.π₀.mk (roofReplacementVertex F c g) =
      SSet.π₀.mk (roofReplacementVertex F d ((F.map r).app (op ⦋0⦌) g)) :=
  SSet.π₀.sound (roofReplacementTransportEdge F r g)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
