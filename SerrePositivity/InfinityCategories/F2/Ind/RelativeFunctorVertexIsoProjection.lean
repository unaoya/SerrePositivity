module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeVertexIsoCylinder
public import SerrePositivity.InfinityCategories.F1.Fibrations.VertexFiberIsoProjection
/-!
概要：相対関手空間内の指定同型を、元の全族の同型とその射影の等号へ移す。
方針：fiber の包含で写し、定値となる後合成の同型を計算する。
規約：相対関手空間の充填性を仮定しない。使われ方：指定始点下の実 comma の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
  (f g : A ⟶ E) (hf : f ≫ p = a) (hg : g ≫ p = a)
  (e : VertexIso (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg))
/-- 概要：指定相対同型を、そのまま元の全族の同型へ写す。
方針：相対関手空間の包含で写す。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
def relativeFunctorVertexIsoImage : FunctorIso f g :=
  VertexIso.map e (vertexFiberι ((ihom A).map p) (functorVertex a))
/-- 概要：同じ指定同型の後合成は、元の端点の等号の同型そのもの。
方針：fiber の射影の等号同型を回収する。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
lemma relativeFunctorVertexIsoImage_postcomp :
    (relativeFunctorVertexIsoImage p a f g hf hg e).postcomp p =
      eqToIso (congrArg (fun v : A ⟶ B => SSet.HomotopyCategory.mk (functorVertex v))
        (hf.trans hg.symm)) := by
  have hh := congrArg Iso.hom
    (VertexIso.map_vertexFiber_projection ((ihom A).map p) (functorVertex a) e)
  apply Iso.ext
  change (FunctorIso.postcomp
    (show FunctorIso f g from VertexIso.map e
      (vertexFiberι ((ihom A).map p) (functorVertex a))) p).hom = _
  simp only [FunctorIso.postcomp, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    eqToHom_refl, Category.id_comp, Category.comp_id, CategoryTheory.Functor.mapIso_hom]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, eqToHom_trans] at hh
  exact hh
end SerrePositivity.InfinityCategories.F2.Ind
