module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictLeftSectionBifunctor

/-!
概要：相対切断のパラメータ・定義域・値域を同時に動かすときの、同じ全評価の公式。
方針：元の前合成と後合成の包含式を uncurry し、二射影で評価する。
規約：全ての射と底上の可換性を厳密に保持し、充填性は要求しない。
使われ方：全単体の切断の replacement の面・退化の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 底上の一般の前合成を全評価へ戻す。 -/
lemma relativeFunctorUncurry_overPre {E B T : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (r : a ⟶ b) (θ : T ⟶ relativeFunctorSpace p b.hom) :
    relativeFunctorUncurry (θ ≫ relativeFunctorOverPre p r) =
      r.left ▷ T ≫ relativeFunctorUncurry θ := by
  rw [relativeFunctorUncurry, Category.assoc, relativeFunctorOverPre_ι,
    ← Category.assoc, uncurry_pre_app]
  rfl

/-- 定義域・パラメータ・全空間の元の射を動かす、一つの全評価公式。 -/
lemma relativeFunctorUncurry_mixedParameter {X Y B T U : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ B) (f : X ⟶ Y) (hf : f ≫ q = p)
    {a b : Over B} (r : a ⟶ b) (θ : T ⟶ relativeFunctorSpace p b.hom) (k : U ⟶ T) :
    relativeFunctorUncurry (((k ≫ θ) ≫
      HomotopyLimits.relativeFunctorPost p q f hf b.hom) ≫ relativeFunctorOverPre q r) =
      r.left ▷ U ≫ (b.left ◁ k) ≫ relativeFunctorUncurry θ ≫ f := by
  rw [relativeFunctorUncurry_overPre, HomotopyLimits.relativeFunctorUncurry_post,
    relativeFunctorUncurry_parameter, Category.assoc]

/-- 同じ全評価を対角に制限しても、三つの元の射の合成を厳密に回収する。 -/
lemma relativeSection_mixedDiagonal {X Y B T U V : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ B) (f : X ⟶ Y) (hf : f ≫ q = p)
    {a b : Over B} (r : a ⟶ b) (θ : T ⟶ relativeFunctorSpace p b.hom) (k : U ⟶ T)
    (v : V ⟶ a.left) (x : V ⟶ U) :
    lift v x ≫ relativeFunctorUncurry (((k ≫ θ) ≫
      HomotopyLimits.relativeFunctorPost p q f hf b.hom) ≫ relativeFunctorOverPre q r) =
      lift (v ≫ r.left) (x ≫ k) ≫ relativeFunctorUncurry θ ≫ f := by
  rw [relativeFunctorUncurry_mixedParameter]
  simp only [← Category.assoc, lift_whiskerRight, lift_whiskerLeft]

end SerrePositivity.InfinityCategories.F2.Ind
