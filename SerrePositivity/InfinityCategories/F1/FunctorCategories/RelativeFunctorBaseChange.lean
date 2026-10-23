module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace

/-!
概要：引き戻した射への相対関手空間と、合成した底の図式への相対関手空間の同型。
方針：パラメーター付きの評価を引き戻しの普遍性で往復する。
規約：すべて通常の単体集合の同型であり、充填性は不要。
使われ方：Kerodon Remark 5.6.2.5、unstraightening の変換の選択を底上の写像空間へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：相対 uncurry はパラメーターの射による前合成と可換。
方針：内部 Hom の uncurry の自然性を使う。
規約：元の図式の定義域 A は固定する。
使われ方：Kerodon §5.3.1、パラメーター付き比較の等式の検査。 -/
lemma relativeFunctorUncurry_naturality {A T U E B : SSet.{u}}
    {p : E ⟶ B} {a : A ⟶ B} (f : U ⟶ relativeFunctorSpace p a) (k : T ⟶ U) :
    relativeFunctorUncurry (k ≫ f) = (A ◁ k) ≫ relativeFunctorUncurry f := by
  exact (uncurry_natural_left k (f ≫ vertexFiberι _ _)).symm

/-- 概要：引き戻した射への相対関手を元の射への相対関手へ送る。
方針：引き戻しの第一射影をパラメーター付き評価に後合成する。
規約：固定する底の図式は a から a≫f に変わる。
使われ方：Kerodon Remark 5.6.2.5、引き戻しに沿う相対写像空間の比較。 -/
noncomputable def relativeFunctorBaseChangeForward {A E B D : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D) :
    relativeFunctorSpace (pullback.snd p f) a ⟶ relativeFunctorSpace p (a ≫ f) :=
  relativeFunctorCurry (relativeFunctorUncurry (𝟙 _) ≫ pullback.fst p f) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      relativeFunctorUncurry_projection, Category.assoc])

/-- 概要：合成した底の図式への相対関手を引き戻した射への相対関手へ戻す。
方針：評価と固定された底の図式を引き戻しへ持ち上げる。
規約：パラメーター依存の底は第一射影で忘れる。
使われ方：Kerodon Remark 5.6.2.5、相対写像空間の底変換の逆射。 -/
noncomputable def relativeFunctorBaseChangeBackward {A E B D : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D) :
    relativeFunctorSpace p (a ≫ f) ⟶ relativeFunctorSpace (pullback.snd p f) a :=
  relativeFunctorCurry
    (pullback.lift (relativeFunctorUncurry (𝟙 _)) (fst A _ ≫ a) (by
      rw [relativeFunctorUncurry_projection, Category.assoc]))
    (pullback.lift_snd _ _ _)

/-- 概要：底変換の順方向を評価すると第一射影への後合成になる。
方針：パラメーター自然性と相対 curry の往復を使う。
規約：任意のパラメーター T からの族で成り立つ。
使われ方：Kerodon Remark 5.6.2.5、底変換の同型の計算則。 -/
lemma relativeFunctorBaseChangeForward_uncurry {A E B D T : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D)
    (k : T ⟶ relativeFunctorSpace (pullback.snd p f) a) :
    relativeFunctorUncurry (k ≫ relativeFunctorBaseChangeForward p f a) =
      relativeFunctorUncurry k ≫ pullback.fst p f := by
  rw [relativeFunctorUncurry_naturality, relativeFunctorBaseChangeForward,
    relativeFunctorUncurry_curry, ← Category.assoc]
  have h := relativeFunctorUncurry_naturality (𝟙 (relativeFunctorSpace (pullback.snd p f) a)) k
  rw [Category.comp_id] at h
  rw [← h]

/-- 概要：底変換の逆方向を評価すると引き戻しへの持ち上げになる。
方針：相対 curry の往復と引き戻しの二射影で確認する。
規約：同型の逆射をパラメーター付きの族に適用した計算。
使われ方：Kerodon Remark 5.6.2.5、底変換の往復の検証。 -/
lemma relativeFunctorBaseChangeBackward_uncurry {A E B D T : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D)
    (k : T ⟶ relativeFunctorSpace p (a ≫ f)) :
    relativeFunctorUncurry (k ≫ relativeFunctorBaseChangeBackward p f a) =
      pullback.lift (relativeFunctorUncurry k) (fst A T ≫ a) (by
        rw [relativeFunctorUncurry_projection, Category.assoc]) := by
  rw [relativeFunctorUncurry_naturality, relativeFunctorBaseChangeBackward,
    relativeFunctorUncurry_curry]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    have h := relativeFunctorUncurry_naturality (𝟙 (relativeFunctorSpace p (a ≫ f))) k
    simpa only [Category.comp_id] using h.symm
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc,
      whiskerLeft_fst]

/-- 概要：引き戻した射への相対関手空間は、合成した底の図式への相対関手空間と同型。
方針：評価の計算則と引き戻しの二射影で両往復を確認する。
規約：単なる同値ではなく単体集合の同型。
使われ方：Kerodon Remark 5.6.2.5、unstraightening の写像空間の底変換。 -/
noncomputable def relativeFunctorBaseChangeIso {A E B D : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D) :
    relativeFunctorSpace (pullback.snd p f) a ≅ relativeFunctorSpace p (a ≫ f) where
  hom := relativeFunctorBaseChangeForward p f a
  inv := relativeFunctorBaseChangeBackward p f a
  hom_inv_id := by
    apply relativeFunctorUncurry_injective (pullback.snd p f) a
    rw [relativeFunctorBaseChangeBackward_uncurry]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, relativeFunctorBaseChangeForward, relativeFunctorUncurry_curry]
    · rw [pullback.lift_snd, relativeFunctorUncurry_projection]
  inv_hom_id := by
    apply relativeFunctorUncurry_injective p (a ≫ f)
    rw [relativeFunctorBaseChangeForward_uncurry, relativeFunctorBaseChangeBackward]
    rw [relativeFunctorUncurry_curry, pullback.lift_fst]

end SerrePositivity.InfinityCategories
