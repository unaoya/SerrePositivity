module

public import SerrePositivity.InfinityCategories.F2.SmallRelativeSourceRestriction
public import SerrePositivity.InfinityCategories.F2.SmallRelativeVertexIsoPresentation

/-!
概要：元の指定相対同型を小宇宙へ降ろして制限する操作を元の始域制限へ移す。
方針：縮小の厳密な交換式を指定同型へ作用させ、同じ指定値の下降を保つ。
規約：両端の元の射と底上の条件を保持。使われ方：小さい三角形比較の fiber 制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 小さい指定比較の制限は元の同じ比較を先に始域制限して下降した値になる。 -/
lemma smallRelativeVertexIso_pre_heq_restrict_down {B C : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    {f g : leftUnstraightening F ⟶ leftUnstraightening G}
    (hf : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (hg : g ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (e : VertexIso (relativeFunctorVertex _ _ f hf) (relativeFunctorVertex _ _ g hg))
    (s : C ⟶ smallLeftUnstraightening F) :
    HEq
      (VertexIso.map (smallUnstraighteningRelativeVertexIso F G hf hg e)
        (relativeFunctorPre (smallLeftUnstraighteningProjection G)
          (smallLeftUnstraighteningProjection F) s))
      (downVertexIso
        (VertexIso.map
          (VertexIso.map e (relativeFunctorOverPre (leftUnstraighteningProjection G)
            (smallUnstraighteningSourceRestriction F s)))
          (smallUnstraighteningSourceRelativeIso G
            (s ≫ smallLeftUnstraighteningProjection F)).inv)) := by
  let a := (smallLeftUnstraighteningRelativeFunctorIso F G).inv
  let b := (SSet.uliftFunctor.{u + 1, u}).map
    (relativeFunctorPre (smallLeftUnstraighteningProjection G)
      (smallLeftUnstraighteningProjection F) s)
  let c := relativeFunctorOverPre (leftUnstraighteningProjection G)
    (smallUnstraighteningSourceRestriction F s)
  let d := (smallUnstraighteningSourceRelativeIso G
    (s ≫ smallLeftUnstraighteningProjection F)).inv
  have hc : a ≫ b = c ≫ d := smallRelativeFunctorIso_inv_pre F G s
  have hm := (heq_of_eq (vertexIso_map_comp e a b)).trans
    ((vertexIso_map_heq e hc).trans (heq_of_eq (vertexIso_map_comp e c d)).symm)
  have hs := congrArg (fun k => k.app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex _ _ f hf)) hc
  have ht := congrArg (fun k => k.app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex _ _ g hg)) hc
  exact (smallRelativeVertexIso_pre_heq_down_map F G hf hg e s).trans
    (downVertexIso_heq_of_heq _ _ hs ht hm)

end SerrePositivity.InfinityCategories.F2
