module

public import SerrePositivity.InfinityCategories.HA.Monads.OppositeOrdinalActionLaws

/-!
概要：二つの混合Homの間に自己Homを挟む水平合成の全結合則。
方針：実区間表示の厳密な往復と忠実な包含で、元の順序和の結合則へ戻す。
規約：全ての射と空の自己Homを含む関手の等式。
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

/-- 概要：混合合成を区間表示へ送ると、元の両端点保存の順序和に戻る。
方針：実区間同値の厳密な余単位を使う。
規約：全射の自然性を含む。使われ方：Riehl–Verity Remark 3.3.8 のirの因子化。 -/
lemma mixedBottomTopOrdinal_representation :
    mixedBottomTopOrdinal ⋙ ordinalIntervalRepresentation = bottomTopIntervalSum := by
  change bottomTopIntervalSum ⋙
    (ordinalIntervalEquivalence.inverse ⋙ ordinalIntervalRepresentation) = bottomTopIntervalSum
  rw [ordinalInterval_target_roundtrip, CategoryTheory.Functor.comp_id]

/-- 概要：混合区間の順序和を忘却すると元の増大単体圏の順序和。
方針：射は構成済みの同じtensorHomOfであることを使う。
規約：元の二つの変数を保つ。使われ方：Riehl–Verity Remark 3.3.8 の水平合成の比較。 -/
lemma bottomTopIntervalSum_forget :
    bottomTopIntervalSum ⋙ endpointAugmentedForget simplexPreservesEndpoints =
      (endpointAugmentedForget simplexPreservesBottom).prod
        (endpointAugmentedForget simplexPreservesTop) ⋙ tensor AugmentedSimplexCategory := rfl

variable {I : Type u} [Category.{v} I]

/-- 概要：実区間表示へ送った全関手の等式を元へ戻す。
方針：構成済みの厳密な逆へ後合成する。
規約：同じ増大単体圏の反対の上。使われ方：HA Proposition 4.7.3.3 の全合成の回収。 -/
lemma ordinalIntervalRepresentation_comp_injective
    {F G : I ⥤ AugmentedSimplexCategoryᵒᵖ}
    (h : F ⋙ ordinalIntervalRepresentation = G ⋙ ordinalIntervalRepresentation) : F = G := by
  have h' := congrArg (fun K => K ⋙ ordinalIntervalEquivalence.inverse) h
  change F ⋙ (ordinalIntervalRepresentation ⋙ ordinalIntervalEquivalence.inverse) =
    G ⋙ (ordinalIntervalRepresentation ⋙ ordinalIntervalEquivalence.inverse) at h'
  simpa only [ordinalInterval_source_roundtrip, CategoryTheory.Functor.comp_id] using h'

/-- 概要：二つの混合Homの関手の全合成を、忘却した順序和で評価する。
方針：区間表示での因子化と両端点の忘却比較に前合成する。
規約：全Iの射を残す。使われ方：HA Proposition 4.7.3.3 の水平結合則。 -/
lemma mixedBottomTopFunctor_forget (F : I ⥤ BottomSimplexCategory)
    (G : I ⥤ TopSimplexCategory) :
    ((F.prod' G ⋙ mixedBottomTopOrdinal) ⋙ ordinalIntervalRepresentation) ⋙
        endpointAugmentedForget simplexPreservesEndpoints =
      (F ⋙ endpointAugmentedForget simplexPreservesBottom).prod'
        (G ⋙ endpointAugmentedForget simplexPreservesTop) ⋙ tensor AugmentedSimplexCategory := by
  have h := congrArg
    (fun K => (F.prod' G ⋙ K) ⋙ endpointAugmentedForget simplexPreservesEndpoints)
    mixedBottomTopOrdinal_representation
  simp only [CategoryTheory.Functor.assoc, bottomTopIntervalSum_forget] at h
  exact h

/-- 概要：最小元保存・自己Hom・最大元保存の三重合成の全結合則。
方針：忠実な区間表示で忘却し、元の順序和の全結合則を使う。
規約：自己Homの空と全射を含む。使われ方：Riehl–Verity Remark 3.3.8 の-++-の合成。 -/
lemma mixedBottomTopFunctor_balance (F : I ⥤ BottomSimplexCategory)
    (G : I ⥤ AugmentedSimplexCategory) (H : I ⥤ TopSimplexCategory) :
    ((F.prod' G ⋙ bottomOrdinalAction).prod' H ⋙ mixedBottomTopOrdinal) =
      (F.prod' (G.prod' H ⋙ topOrdinalAction) ⋙ mixedBottomTopOrdinal) := by
  apply ordinalIntervalRepresentation_comp_injective
  apply endpointAugmentedForget_comp_injective simplexPreservesEndpoints
  rw [mixedBottomTopFunctor_forget, mixedBottomTopFunctor_forget,
    bottomOrdinalActionFunctor_forget, topOrdinalActionFunctor_forget]
  exact ordinalSumFunctor_assoc
    (F ⋙ endpointAugmentedForget simplexPreservesBottom) G
    (H ⋙ endpointAugmentedForget simplexPreservesTop)

/-- 概要：逆順の混合合成の反対はGalois双対に送った元の混合合成。
方針：構成した実双関手の反対と二重反対を展開する。
規約：全関手を同じ添字圏の反対へ送る。使われ方：Riehl–Verity Remark 3.3.8 の双対。 -/
lemma mixedTopBottomFunctor_op (F : I ⥤ TopSimplexCategory)
    (G : I ⥤ BottomSimplexCategory) :
    (F.prod' G ⋙ mixedTopBottomOrdinal).op =
      (F ⋙ topToBottomOpEquivalence.functor).leftOp.prod'
        (G ⋙ endpointSimplexEquivalence.functor).leftOp ⋙ mixedBottomTopOrdinal := rfl

/-- 概要：最大元保存・反対の自己Hom・最小元保存の三重合成の全結合則。
方針：Galois双対に送った二つの作用と、証明済みの混合結合則を使う。
規約：全単体に使える全関手の等式。使われ方：Riehl–Verity Remark 3.3.8 の+--+の合成。 -/
lemma mixedTopBottomFunctor_balance (F : I ⥤ TopSimplexCategory)
    (G : I ⥤ AugmentedSimplexCategoryᵒᵖ) (H : I ⥤ BottomSimplexCategory) :
    ((F.prod' G ⋙ topOppositeOrdinalAction).prod' H ⋙ mixedTopBottomOrdinal) =
      (F.prod' (G.prod' H ⋙ bottomOppositeOrdinalAction) ⋙ mixedTopBottomOrdinal) := by
  have h :
      (((F.prod' G ⋙ topOppositeOrdinalAction).prod' H ⋙ mixedTopBottomOrdinal)).op =
        (F.prod' (G.prod' H ⋙ bottomOppositeOrdinalAction) ⋙ mixedTopBottomOrdinal).op := by
    rw [mixedTopBottomFunctor_op, mixedTopBottomFunctor_op,
      topOppositeOrdinalActionFunctor_dual, bottomOppositeOrdinalActionFunctor_dual]
    exact mixedBottomTopFunctor_balance
      (F ⋙ topToBottomOpEquivalence.functor).leftOp G.leftOp
      (H ⋙ endpointSimplexEquivalence.functor).leftOp
  exact congrArg (fun K : Iᵒᵖ ⥤ AugmentedSimplexCategoryᵒᵖ => K.unop) h

end SerrePositivity.InfinityCategories.HA.Monads
