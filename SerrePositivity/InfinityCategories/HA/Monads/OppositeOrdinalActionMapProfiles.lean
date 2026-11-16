module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalActionMapProfiles

/-!
概要：反対側の二つの水平作用の全射を端点共有の有限単調射として照合する。
方針：元の作用の全射の表示を実随伴へ移し、構成済みのGalois条件と一意性を使う。
規約：空の自己Homの因子も含む。存在を仮定する新しいinstanceは置かない。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の全水平結合則。
Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：最大元保存の反対側の右作用の全射は区間表示との端点共有。
方針：元の最小元保存の作用の射を正規化し、同じ実右随伴を比較する。
規約：自己Homの空も許す。使われ方：HA Proposition 4.7.3.3 の混合水平結合則。 -/
lemma topOppositeOrdinalAction_map_heq {A B : AugmentedSimplexCategoryᵒᵖ}
    {X Y : TopSimplexCategory} (f : X ⟶ Y) (g : A ⟶ B) :
    HEq (topOppositeOrdinalAction.map (X := (X, A)) (Y := (Y, B)) (f, g)).hom.toOrderHom
      (ordinalGlue f.hom.toOrderHom (ordinalIntervalMap (augmentedOrderHom g.unop))) := by
  let l := topSimplexLeftAdjoint f
  let h := bottomOrdinalAction.map
    (X := ((⟨Y.obj⟩ : BottomSimplexCategory), B.unop))
    (Y := ((⟨X.obj⟩ : BottomSimplexCategory), A.unop)) (l, g.unop)
  let k := ordinalAppendNonempty l.hom.toOrderHom (augmentedOrderHom g.unop)
  have hk₀ : k 0 = 0 :=
    ordinalAppendNonempty_zero _ _ (ordinalLeftAdjoint_zero f.hom.toOrderHom f.property)
  have hh : HEq h.hom.toOrderHom k :=
    (bottomOrdinalAction_map_heq l g.unop).trans (ordinalAppendNonempty_heq _ _).symm
  have hr := ordinalRightAdjoint_heq
    (bottomOrdinalAction_len (⟨Y.obj⟩ : BottomSimplexCategory) B.unop)
    (bottomOrdinalAction_len (⟨X.obj⟩ : BottomSimplexCategory) A.unop)
    h.property hk₀ hh
  change HEq (ordinalRightAdjoint h.hom.toOrderHom h.property)
    (ordinalGlue f.hom.toOrderHom (ordinalIntervalMap (augmentedOrderHom g.unop)))
  exact hr.trans (heq_of_eq
    (ordinalRightAdjoint_append_glue f.hom.toOrderHom f.property (augmentedOrderHom g.unop)))

/-- 概要：最小元保存の反対側の左作用の全射も区間表示との端点共有。
方針：元の最大元保存の作用の全射を実左随伴へ移す。
規約：空から非空へ動く自己Homの射も含む。使われ方：HA Proposition 4.7.3.3 の全結合則。 -/
lemma bottomOppositeOrdinalAction_map_heq {A B : AugmentedSimplexCategoryᵒᵖ}
    {X Y : BottomSimplexCategory} (f : A ⟶ B) (g : X ⟶ Y) :
    HEq (bottomOppositeOrdinalAction.map (X := (A, X)) (Y := (B, Y)) (f, g)).hom.toOrderHom
      (ordinalGlue (ordinalIntervalMap (augmentedOrderHom f.unop)) g.hom.toOrderHom) := by
  let r := bottomSimplexRightAdjoint g
  let h := topOrdinalAction.map
    (X := (B.unop, (⟨Y.obj⟩ : TopSimplexCategory)))
    (Y := (A.unop, (⟨X.obj⟩ : TopSimplexCategory))) (f.unop, r)
  let k := ordinalAppend (augmentedOrderHom f.unop) r.hom.toOrderHom
  have hk₁ : k (Fin.last (augmentedOrdinalCard B.unop + Y.obj.len)) =
      Fin.last (augmentedOrdinalCard A.unop + X.obj.len) :=
    ordinalAppend_last _ _ (ordinalRightAdjoint_last g.hom.toOrderHom g.property)
  have hh : HEq h.hom.toOrderHom k := topOrdinalAction_map_heq f.unop r
  have hl := ordinalLeftAdjoint_heq
    (topOrdinalAction_len B.unop (⟨Y.obj⟩ : TopSimplexCategory))
    (topOrdinalAction_len A.unop (⟨X.obj⟩ : TopSimplexCategory))
    h.property hk₁ hh
  change HEq (ordinalLeftAdjoint h.hom.toOrderHom h.property)
    (ordinalGlue (ordinalIntervalMap (augmentedOrderHom f.unop)) g.hom.toOrderHom)
  exact hl.trans (heq_of_eq
    (ordinalLeftAdjoint_append_glue (augmentedOrderHom f.unop) g.hom.toOrderHom g.property))

end SerrePositivity.InfinityCategories.HA.Monads
