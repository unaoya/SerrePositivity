module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：充満忠実な射は、端点表示を保つ元の指定頂点同型の型付き一致を反映する。
方針：端点の等式を消去し、ホモトピー圏の忠実性で同じ射の値へ戻す。
規約：元の指定同型を保持。使われ方：全 prism 比較と元の fiber 内比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ端点の表示変更を保つ指定同型の値は、充満忠実な射の像から回収できる。 -/
lemma vertexIso_map_reflects_heq {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (f : X ⟶ Y) (hf : IsFullyFaithful f) {x y x' y' : X _⦋0⦌}
    (e : VertexIso x y) (e' : VertexIso x' y') (hx : x = x') (hy : y = y')
    (he : HEq (VertexIso.map e f) (VertexIso.map e' f)) : HEq e e' := by
  subst x' y'
  apply heq_of_eq
  apply Iso.ext
  apply hf.toHoFullyFaithful.map_injective
  exact congrArg Iso.hom (eq_of_heq he)

end SerrePositivity.InfinityCategories.F2
