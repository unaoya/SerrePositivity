module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UniverseVertexIsoRoundTrip
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UniverseHomotopyDownNaturality
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation

/-!
概要：元の端点と指定値を保った宇宙下降の比較を、同じ射で写して再び持ち上げる。
方針：端点等式を明示して写像・持ち上げの HEq を移し、元の指定値の往復を使う。
規約：端点を HEq から抽出しない。使われ方：模型比較の単位後合成と宇宙往復の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 明示した両端等式と同じ指定値は、同じ宇宙持ち上げ後も保持される。 -/
lemma uliftVertexIso_heq_of_heq {X : SSet.{u}} [Quasicategory X]
    {x y x' y' : X _⦋0⦌} (e : VertexIso x y) (e' : VertexIso x' y')
    (hx : x = x') (hy : y = y') (he : HEq e e') :
    HEq (uliftVertexIso.{u, v} e) (uliftVertexIso.{u, v} e') := by
  subst x' y'
  cases eq_of_heq he
  rfl

/-- 同じ下降値を射で写して持ち上げると、元の指定同型の同じ射の持ち上げによる像になる。 -/
lemma uliftVertexIso_mapped_down_heq {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {x y : X _⦋0⦌} {a b : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌}
    (e : VertexIso x y) (d : VertexIso a b) (hx : x = a.down) (hy : y = b.down)
    (he : HEq e (downVertexIso d)) (q : X ⟶ Y) :
    HEq (uliftVertexIso.{u, v} (VertexIso.map e q))
      (VertexIso.map d ((SSet.uliftFunctor.{v, u}).map q)) := by
  have hm := vertexIso_map_heq_of_heq e (downVertexIso d) hx hy he q
  have hu := uliftVertexIso_heq_of_heq (VertexIso.map e q)
    (VertexIso.map (downVertexIso d) q)
    (congrArg (fun z => q.app (Opposite.op ⦋0⦌) z) hx)
    (congrArg (fun z => q.app (Opposite.op ⦋0⦌) z) hy) hm
  rw [downVertexIso_map, uliftVertexIso_downVertexIso] at hu
  exact hu

end SerrePositivity.InfinityCategories.F2
