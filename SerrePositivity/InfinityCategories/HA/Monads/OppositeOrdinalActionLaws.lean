module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalActionComparison

/-!
概要：Galois双対で、反対側の自己Homの積と端点保存の作用の全結合則を移す。
方針：構成済みの双対の厳密な往復を確認し、実関手の等式を反対へ移す。
規約：全自然性を含め、辺だけの照合に弱めない。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 のwalking adjunction。
Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Opposite MonoidalCategory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：最大元保存から最小元保存の反対への双対の全対象側の往復。
方針：既存のGalois双対の往復を二重反対から戻す。
規約：同じ骨格の関手等式。使われ方：Riehl–Verity Remark 3.3.8 の双対側の法則。 -/
lemma topToBottomOp_source_roundtrip :
    topToBottomOpEquivalence.functor ⋙ topToBottomOpEquivalence.inverse =
      𝟭 TopSimplexCategory := by
  exact congrArg
    (fun K : TopSimplexCategoryᵒᵖ ⥤ TopSimplexCategoryᵒᵖ =>
      opOp TopSimplexCategory ⋙ K.op ⋙ unopUnop TopSimplexCategory)
    topSimplex_roundtrip

/-- 概要：同じ双対の反対圏側の往復も恒等関手。
方針：最小元保存のGalois双対の往復の反対を取る。
規約：元の反対圏の射で等しい。使われ方：Riehl–Verity Remark 3.3.8。 -/
lemma topToBottomOp_target_roundtrip :
    topToBottomOpEquivalence.inverse ⋙ topToBottomOpEquivalence.functor =
      𝟭 BottomSimplexCategoryᵒᵖ := by
  exact congrArg (fun K : BottomSimplexCategory ⥤ BottomSimplexCategory => K.op)
    bottomSimplex_roundtrip

variable {I : Type u} [Category.{v} I]

/-- 概要：最小元保存の双対へ送った関手の等式を戻す。
方針：既存の厳密な逆へ後合成する。規約：同じI上の関手。
使われ方：HA Proposition 4.7.3.3 の結合則の回収。 -/
lemma bottomFunctor_eq_of_dual {F G : I ⥤ BottomSimplexCategory}
    (h : F ⋙ endpointSimplexEquivalence.functor = G ⋙ endpointSimplexEquivalence.functor) :
    F = G := by
  have h' := congrArg (fun K => K ⋙ endpointSimplexEquivalence.inverse) h
  change F ⋙ (bottomSimplexToTopOp ⋙ topOpSimplexToBottom) =
    G ⋙ (bottomSimplexToTopOp ⋙ topOpSimplexToBottom) at h'
  simpa only [bottomSimplex_roundtrip, CategoryTheory.Functor.comp_id] using h'

/-- 概要：最大元保存の双対へ送った関手の等式を戻す。
方針：証明済みの厳密な往復に後合成して戻す。
規約：元の関手自体の等式。使われ方：HA Proposition 4.7.3.3 の結合則の回収。 -/
lemma topFunctor_eq_of_dual {F G : I ⥤ TopSimplexCategory}
    (h : F ⋙ topToBottomOpEquivalence.functor = G ⋙ topToBottomOpEquivalence.functor) :
    F = G := by
  have h' := congrArg (fun K => K ⋙ topToBottomOpEquivalence.inverse) h
  change F ⋙ (topToBottomOpEquivalence.functor ⋙ topToBottomOpEquivalence.inverse) =
    G ⋙ (topToBottomOpEquivalence.functor ⋙ topToBottomOpEquivalence.inverse) at h'
  simpa only [topToBottomOp_source_roundtrip, CategoryTheory.Functor.comp_id] using h'

/-- 概要：反対側の最小元保存の作用の双対は元の最大元保存の作用。
方針：作用の実定義と双対の厳密な往復を使う。
規約：全関手の等式として移す。使われ方：Riehl–Verity Remark 3.3.8 の双対側の合成。 -/
lemma bottomOppositeOrdinalActionFunctor_dual (F : I ⥤ AugmentedSimplexCategoryᵒᵖ)
    (G : I ⥤ BottomSimplexCategory) :
    (F.prod' G ⋙ bottomOppositeOrdinalAction) ⋙ endpointSimplexEquivalence.functor =
      (F.leftOp.prod' (G ⋙ endpointSimplexEquivalence.functor).leftOp ⋙
        topOrdinalAction).rightOp := by
  let K := F.leftOp.prod' (G ⋙ endpointSimplexEquivalence.functor).leftOp ⋙ topOrdinalAction
  change (K.rightOp ⋙ endpointSimplexEquivalence.inverse) ⋙
    endpointSimplexEquivalence.functor = K.rightOp
  change K.rightOp ⋙ (topOpSimplexToBottom ⋙ bottomSimplexToTopOp) = K.rightOp
  rw [topSimplex_roundtrip, CategoryTheory.Functor.comp_id]

/-- 概要：反対側の最大元保存の作用の双対は元の最小元保存の作用。
方針：構成した実双関手と双対の余単位を厳密に照合する。
規約：全Iの射に関する等式。使われ方：Riehl–Verity Remark 3.3.8。 -/
lemma topOppositeOrdinalActionFunctor_dual (F : I ⥤ TopSimplexCategory)
    (G : I ⥤ AugmentedSimplexCategoryᵒᵖ) :
    (F.prod' G ⋙ topOppositeOrdinalAction) ⋙ topToBottomOpEquivalence.functor =
      ((F ⋙ topToBottomOpEquivalence.functor).leftOp.prod' G.leftOp ⋙
        bottomOrdinalAction).rightOp := by
  let K := (F ⋙ topToBottomOpEquivalence.functor).leftOp.prod' G.leftOp ⋙ bottomOrdinalAction
  change (K.rightOp ⋙ topToBottomOpEquivalence.inverse) ⋙
    topToBottomOpEquivalence.functor = K.rightOp
  rw [CategoryTheory.Functor.assoc, topToBottomOp_target_roundtrip,
    CategoryTheory.Functor.comp_id]

/-- 概要：反対側の増大単体圏の順序和の全結合則。
方針：元の全結合則の反対を取る。規約：任意のI上の三つの関手。
使われ方：HA §4.7.2 の反対側の自己Homの合成。 -/
lemma oppositeOrdinalSumFunctor_assoc (F G H : I ⥤ AugmentedSimplexCategoryᵒᵖ) :
    ((F.prod' G ⋙ walkingAdjunctionHorizontal .minus .minus .minus).prod' H ⋙
      walkingAdjunctionHorizontal .minus .minus .minus) =
      (F.prod' (G.prod' H ⋙ walkingAdjunctionHorizontal .minus .minus .minus) ⋙
        walkingAdjunctionHorizontal .minus .minus .minus) := by
  exact congrArg (fun K : Iᵒᵖ ⥤ AugmentedSimplexCategory => K.rightOp)
    (ordinalSumFunctor_assoc F.leftOp G.leftOp H.leftOp)

/-- 概要：反対側の最小元保存の左作用の全結合則。
方針：双対へ送り、元の最大元保存の左作用の全結合則を使う。
規約：全単体に使える関手等式。使われ方：HA Proposition 4.7.3.3 の水平結合則。 -/
lemma bottomOppositeOrdinalActionFunctor_assoc
    (F G : I ⥤ AugmentedSimplexCategoryᵒᵖ) (H : I ⥤ BottomSimplexCategory) :
    ((F.prod' G ⋙ walkingAdjunctionHorizontal .minus .minus .minus).prod' H ⋙
      bottomOppositeOrdinalAction) =
      (F.prod' (G.prod' H ⋙ bottomOppositeOrdinalAction) ⋙ bottomOppositeOrdinalAction) := by
  apply bottomFunctor_eq_of_dual
  rw [bottomOppositeOrdinalActionFunctor_dual, bottomOppositeOrdinalActionFunctor_dual,
    bottomOppositeOrdinalActionFunctor_dual]
  exact congrArg (fun K : Iᵒᵖ ⥤ TopSimplexCategory => K.rightOp)
    (topOrdinalActionFunctor_assoc F.leftOp G.leftOp
      (H ⋙ endpointSimplexEquivalence.functor).leftOp)

/-- 概要：反対側の最大元保存の右作用の全結合則。
方針：Galois双対の実関手で元の最小元保存の右作用の結合則へ戻す。
規約：全Iの射を含める。使われ方：HA Proposition 4.7.3.3 の水平結合則。 -/
lemma topOppositeOrdinalActionFunctor_assoc (F : I ⥤ TopSimplexCategory)
    (G H : I ⥤ AugmentedSimplexCategoryᵒᵖ) :
    ((F.prod' G ⋙ topOppositeOrdinalAction).prod' H ⋙ topOppositeOrdinalAction) =
      (F.prod' (G.prod' H ⋙ walkingAdjunctionHorizontal .minus .minus .minus) ⋙
        topOppositeOrdinalAction) := by
  apply topFunctor_eq_of_dual
  rw [topOppositeOrdinalActionFunctor_dual, topOppositeOrdinalActionFunctor_dual,
    topOppositeOrdinalActionFunctor_dual]
  exact congrArg (fun K : Iᵒᵖ ⥤ BottomSimplexCategory => K.rightOp)
    (bottomOrdinalActionFunctor_assoc (F ⋙ topToBottomOpEquivalence.functor).leftOp
      G.leftOp H.leftOp)

end SerrePositivity.InfinityCategories.HA.Monads
