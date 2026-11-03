module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallTotalHomShrinkPost
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UniverseMappedIsoRoundTrip

/-!
概要：元の全空間比較の縮小・後合成・再持ち上げ・始域復元を同じ指定値へ戻す。
方針：明示した実頂点で下降の往復を消し、全 Hom の後合成の厳密な式を使う。
規約：元の比較と後合成射を保持。使われ方：模型三角形の指定値と単位後の三角形の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  {f g : leftUnstraightening F ⟶ leftUnstraightening G} (e : FunctorIso f g)

/-- 同じ縮小比較を後合成し再持ち上げすると、元の指定比較の同じ後合成に一致する。 -/
lemma smallUnstraighteningFunctorIso_post_lift_cancel (Z : SSet.{u}) [Quasicategory Z]
    (w : smallLeftUnstraightening G ⟶ Z) :
    HEq (VertexIso.map (uliftVertexIso.{u, u + 1}
      ((smallUnstraighteningFunctorIso F G e).postcomp w)) (smallUnstraighteningHomIso F Z).inv)
      (e.postcomp ((smallLeftUnstraighteningIso G).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map w)) := by
  let Q := smallTotalHomShrink F G
  let d := VertexIso.map e Q
  let e₀ := smallUnstraighteningFunctorIso F G e
  let q := (ihom (smallLeftUnstraightening F)).map w
  have hx : functorVertex (smallLeftUnstraighteningOverMap F G f) =
      (Q.app (Opposite.op ⦋0⦌) (functorVertex f)).down :=
    (congrArg ULift.down (smallTotalHomShrink_vertex F G f)).symm
  have hy : functorVertex (smallLeftUnstraighteningOverMap F G g) =
      (Q.app (Opposite.op ⦋0⦌) (functorVertex g)).down :=
    (congrArg ULift.down (smallTotalHomShrink_vertex F G g)).symm
  have hd := uliftVertexIso_mapped_down_heq e₀ d hx hy
    (smallUnstraighteningFunctorIso_heq_down_image F G e) q
  have he := (uliftVertexIso_heq_of_heq (e₀.postcomp w) (VertexIso.map e₀ q) rfl rfl
    (functorIso_postcomp_vertexMap_heq e₀ w)).trans hd
  have hxf : ULift.up (functorVertex (smallLeftUnstraighteningOverMap F G f ≫ w)) =
      ((SSet.uliftFunctor.{u + 1, u}).map q).app (Opposite.op ⦋0⦌)
        (Q.app (Opposite.op ⦋0⦌) (functorVertex f)) :=
    congrArg (fun z => ULift.up (q.app (Opposite.op ⦋0⦌) z)) hx
  have hyg : ULift.up (functorVertex (smallLeftUnstraighteningOverMap F G g ≫ w)) =
      ((SSet.uliftFunctor.{u + 1, u}).map q).app (Opposite.op ⦋0⦌)
        (Q.app (Opposite.op ⦋0⦌) (functorVertex g)) :=
    congrArg (fun z => ULift.up (q.app (Opposite.op ⦋0⦌) z)) hy
  have hm := vertexIso_map_heq_of_heq (uliftVertexIso.{u, u + 1} (e₀.postcomp w))
    (VertexIso.map d ((SSet.uliftFunctor.{u + 1, u}).map q)) hxf hyg he
    (smallUnstraighteningHomIso F Z).inv
  rw [vertexIso_map_comp, vertexIso_map_comp] at hm
  exact (hm.trans (vertexIso_map_heq e (smallTotalHomShrink_post_cancel F G Z w))).trans
    (functorIso_postcomp_vertexMap_heq e
      ((smallLeftUnstraighteningIso G).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map w)).symm

end SerrePositivity.InfinityCategories.F2
