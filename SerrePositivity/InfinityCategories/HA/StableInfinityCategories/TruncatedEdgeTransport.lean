module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreComparisonConeComposite
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreSourceComparisons

/-!
概要：実 θ と元の始点の比較辺の合成を、同じ錐の圏で照合する。
方針：正規化した制限と全三辺を保持する実二単体を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第一合成式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open SimplicialObject.Truncated
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma truncatedEdge_cast_edge {S : SSet.Truncated.{u} 2}
    {x y x' y' : S _⦋0⦌₂} (e : Truncated.Edge (X := S) x y)
    (h : Truncated.Edge (X := S) x y = Truncated.Edge (X := S) x' y')
    (hx : x = x') (hy : y = y') : (cast h e).edge = e.edge := by
  cases hx
  cases hy
  rfl

lemma homMk_eqToHom_comp_of_edge_eq {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x z)
    (f : Truncated.Edge (X := (truncation 2).obj X) y z)
    (h : x = y) (hef : e.edge = f.edge) :
    Truncated.HomotopyCategory.homMk e =
      eqToHom (congrArg (fun a ↦ (HomotopyCategory.mk a : hoFunctor.obj X)) h) ≫
        Truncated.HomotopyCategory.homMk f := by
  subst y
  have he : e = f := Truncated.Edge.ext hef
  rw [he, eqToHom_refl, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
