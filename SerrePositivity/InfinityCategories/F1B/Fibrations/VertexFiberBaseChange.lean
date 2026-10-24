module

public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalVertexFiberPullback

/-!
概要：引き戻し後の頂点 fiber と元の対応する頂点 fiber の同型。
方針：第一射影と定値な第二射影で両方向を構成する。
規約：fibration 性や単射性は不要。
使われ方：終点 fiber を共通に使う cofinality の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：引き戻した射の頂点 fiber は元の fiber と厳密に同型。
方針：射影を fiber に持ち上げ、逆は定値な第二射影との対で作る。
規約：底の頂点の像は f.app で指定する。
使われ方：引き戻しの包含と元の終点 fiber の包含の比較。 -/
noncomputable def cofinalVertexFiberBaseChangeIso {E A B : SSet.{u}}
    (p : E ⟶ B) (f : A ⟶ B) (a : A _⦋0⦌) :
    vertexFiber (pullback.snd p f) a ≅ vertexFiber p (f.app _ a) where
  hom := vertexFiberLift p (f.app _ a)
    (vertexFiberι (pullback.snd p f) a ≫ pullback.fst p f) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, vertexFiberι_comp,
        SSet.const_comp])
  inv := vertexFiberLift (pullback.snd p f) a
    (pullback.lift (vertexFiberι p (f.app _ a)) (SSet.const a) (by
      rw [vertexFiberι_comp, SSet.const_comp])) (pullback.lift_snd _ _ _)
  hom_inv_id := by
    apply vertexFiber_hom_ext (pullback.snd p f) a
    rw [Category.assoc, vertexFiberLift_ι, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, vertexFiberLift_ι]
    · rw [Category.assoc, pullback.lift_snd, SSet.comp_const, vertexFiberι_comp]
  inv_hom_id := by
    apply vertexFiber_hom_ext p (f.app _ a)
    rw [Category.assoc, vertexFiberLift_ι, ← Category.assoc, vertexFiberLift_ι,
      pullback.lift_fst, Category.id_comp]

/-- 概要：fiber の底変換同型は全空間への射影と両立する。
方針：fiber への持ち上げを包含と合成する。
規約：厳密な可換性。
使われ方：共通 fiber からの合成の cofinality。 -/
lemma cofinalVertexFiberBaseChangeIso_hom_ι {E A B : SSet.{u}}
    (p : E ⟶ B) (f : A ⟶ B) (a : A _⦋0⦌) :
    (cofinalVertexFiberBaseChangeIso p f a).hom ≫ vertexFiberι p (f.app _ a) =
      vertexFiberι (pullback.snd p f) a ≫ pullback.fst p f :=
  rfl

end SerrePositivity.InfinityCategories
