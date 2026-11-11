module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreOuterEdgeProjection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreSourceLimitEdges
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreComparisonFirstComposite

/-!
概要：実 θ の第一合成式を、元の内外の pullback 錐の比較辺へ同定する。
方針：正規化した入力制限と同じ頂点射影、極限錐への辺の一意性を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第一条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open SimplicialObject.Truncated
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma homMk_edge_square_of_edge_eq {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y)
    (f : Truncated.Edge (X := (truncation 2).obj X) x' y')
    (hx : x = x') (hy : y = y') (hef : e.edge = f.edge) :
    Truncated.HomotopyCategory.homMk e ≫
      eqToHom (congrArg (fun a ↦ (HomotopyCategory.mk a : hoFunctor.obj X)) hy) =
        eqToHom (congrArg (fun a ↦ (HomotopyCategory.mk a : hoFunctor.obj X)) hx) ≫
          Truncated.HomotopyCategory.homMk f := by
  subst x'
  subst y'
  have h : e = f := Truncated.Edge.ext hef
  simp only [h, eqToHom_refl, Category.comp_id, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
