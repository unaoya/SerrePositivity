module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CofinalFunctorFamilies

/-!
概要：引き戻した射への相対関手空間と、合成した底図式への相対関手空間の同型。
方針：パラメータ付きの評価に引き戻しの普遍性を適用する。
規約：通常の単体集合の厳密な同型で、fibration 性は不要。
使われ方：Kerodon §5.3.1（Tag 035D）、Proposition 7.2.1.6（Tag 02N6） の cofinality の合成。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：相対 uncurry はパラメーターの射による前合成と可換。
方針：内部 Hom の uncurry の自然性を使う。
規約：元の図式の定義域 A は固定する。
使われ方：Kerodon §5.3.1（Tag 035D）、パラメーター付き比較の等式の検査。 -/
lemma cofinalFunctorUncurry_naturality {A T U E B : SSet.{u}}
    {p : E ⟶ B} {a : A ⟶ B} (f : U ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p a) (k : T ⟶ U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry (k ≫ f) = (A ◁ k) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry f := by
  exact (uncurry_natural_left k (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _)).symm

/-- 概要：引き戻した射への相対関手を元の射への相対関手へ送る。
方針：引き戻しの第一射影をパラメーター付き評価に後合成する。
規約：固定する底の図式は a から a≫f に変わる。
使われ方：Kerodon §5.3.1（Tag 035D）、引き戻しに沿う相対写像空間の比較。 -/
noncomputable def cofinalFunctorBaseChangeForward {A E B D : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace (pullback.snd p f) a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p (a ≫ f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry (𝟙 _) ≫ pullback.fst p f) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry_projection, Category.assoc])

/-- 概要：合成した底の図式への相対関手を引き戻した射への相対関手へ戻す。
方針：評価と固定された底の図式を引き戻しへ持ち上げる。
規約：パラメーター依存の底は第一射影で忘れる。
使われ方：Kerodon §5.3.1（Tag 035D）、相対写像空間の底変換の逆射。 -/
noncomputable def cofinalFunctorBaseChangeBackward {A E B D : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p (a ≫ f) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace (pullback.snd p f) a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorCurry
    (pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry (𝟙 _)) (fst A _ ≫ a) (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry_projection, Category.assoc]))
    (pullback.lift_snd _ _ _)

/-- 概要：底変換の順方向を評価すると第一射影への後合成になる。
方針：パラメーター自然性と相対 curry の往復を使う。
規約：任意のパラメーター T からの族で成り立つ。
使われ方：Kerodon §5.3.1（Tag 035D）、底変換の同型の計算則。 -/
lemma cofinalFunctorBaseChangeForward_uncurry {A E B D T : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D)
    (k : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace (pullback.snd p f) a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry (k ≫ cofinalFunctorBaseChangeForward p f a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry k ≫ pullback.fst p f := by
  rw [cofinalFunctorUncurry_naturality, cofinalFunctorBaseChangeForward,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry_curry, ← Category.assoc]
  have h := cofinalFunctorUncurry_naturality (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace (pullback.snd p f) a)) k
  rw [Category.comp_id] at h
  rw [← h]

/-- 概要：底変換の逆方向を評価すると引き戻しへの持ち上げになる。
方針：相対 curry の往復と引き戻しの二射影で確認する。
規約：同型の逆射をパラメーター付きの族に適用した計算。
使われ方：Kerodon §5.3.1（Tag 035D）、底変換の往復の検証。 -/
lemma cofinalFunctorBaseChangeBackward_uncurry {A E B D T : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D)
    (k : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p (a ≫ f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry (k ≫ cofinalFunctorBaseChangeBackward p f a) =
      pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry k) (fst A T ≫ a) (by
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry_projection, Category.assoc]) := by
  rw [cofinalFunctorUncurry_naturality, cofinalFunctorBaseChangeBackward,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry_curry]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    have h := cofinalFunctorUncurry_naturality (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p (a ≫ f))) k
    simpa only [Category.comp_id] using h.symm
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc,
      whiskerLeft_fst]

/-- 概要：引き戻した射への相対関手空間は、合成した底の図式への相対関手空間と同型。
方針：評価の計算則と引き戻しの二射影で両往復を確認する。
規約：単なる同値ではなく単体集合の同型。
使われ方：Kerodon §5.3.1（Tag 035D）、cofinality の写像空間の底変換。 -/
noncomputable def cofinalFunctorBaseChangeIso {A E B D : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace (pullback.snd p f) a ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p (a ≫ f) where
  hom := cofinalFunctorBaseChangeForward p f a
  inv := cofinalFunctorBaseChangeBackward p f a
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry_injective (pullback.snd p f) a
    rw [cofinalFunctorBaseChangeBackward_uncurry]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, cofinalFunctorBaseChangeForward, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry_curry]
    · rw [pullback.lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry_projection]
  inv_hom_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry_injective p (a ≫ f)
    rw [cofinalFunctorBaseChangeForward_uncurry, cofinalFunctorBaseChangeBackward]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry_curry, pullback.lift_fst]

/-- 概要：底変換の同型は底図式の始域の制限と可換。
方針：相対 uncurry により評価へ戻し、第一射影への後合成と制限を交換する。
規約：底図式 a と制限 i は任意。
使われ方：引き戻した fibration の検査から任意の底図式の検査への移送。 -/
lemma cofinalFunctorBaseChangeIso_pre {A D E B C : SSet.{u}}
    (p : E ⟶ B) (f : C ⟶ B) (a : A ⟶ C) (i : D ⟶ A) :
    (cofinalFunctorBaseChangeIso p f a).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre p (a ≫ f) i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre (pullback.snd p f) a i ≫
        (cofinalFunctorBaseChangeIso p f (i ≫ a)).hom := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry_injective p ((i ≫ a) ≫ f)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry
      (cofinalFunctorBaseChangeForward p f a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre p (a ≫ f) i) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre (pullback.snd p f) a i ≫
      cofinalFunctorBaseChangeForward p f (i ≫ a))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorPre_uncurry, cofinalFunctorBaseChangeForward_uncurry]
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorPre_uncurry (pullback.snd p f) a i
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace (pullback.snd p f) a))
  simp only [Category.id_comp] at ht
  rw [ht, cofinalFunctorBaseChangeForward, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry_curry, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
