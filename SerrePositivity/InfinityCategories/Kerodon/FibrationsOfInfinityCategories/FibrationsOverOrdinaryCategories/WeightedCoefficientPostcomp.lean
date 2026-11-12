module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.WeightedTransportUnitEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCoefficientFormula

/-!
概要：weighted nerve の最後の係数評価は係数図式の自然変換と可換である。
方針：底変換の pullback の一意性と、終対象への輸送の自然性を使う。
規約：パラメータと底の単体を固定し、係数だけを変える。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.4.6（Tag 03BB） の係数の自明 Kan fibration の相対充填。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：weighted nerve の底変換は係数の自然変換と可換。
方針：各単体の底と各初区間の係数を計算する。
規約：底の関手にも係数の充填性にも制約を課さない。
使われ方：Kerodon 5.3.3.1（Tag 025X） の底変換の持ち上げの係数自然性。 -/
lemma weightedNerveBaseMap_postcomp {C D : Type u} [Category.{u} C] [Category.{u} D]
    (K : D ⥤ C) {F G : C ⥤ SSet.{u}} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (Functor.whiskerLeft K η) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseMap K G =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseMap K F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η := rfl

/-- 概要：終対象での係数評価は係数図式の自然変換と可換。
方針：最後の係数に終対象への輸送を続け、η の自然性を使う。
規約：底の終対象は固定する。
使われ方：Kerodon 5.3.3.1（Tag 025X） の最後の値での相対的な持ち上げ。 -/
lemma weightedNerveTerminalEvaluation_postcomp {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) {t : C} (ht : IsTerminal t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveTerminalEvaluation G ht =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveTerminalEvaluation F ht ≫ η.app t := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, τ⟩
  change SSet.yonedaEquiv ((τ.app (Fin.last n) ≫ η.app (σ.obj (Fin.last n))) ≫
      G.map (ht.from (σ.obj (Fin.last n)))) =
    (η.app t).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (τ.app (Fin.last n) ≫ F.map (ht.from (σ.obj (Fin.last n)))))
  rw [← SSet.yonedaEquiv_comp]
  apply congrArg SSet.yonedaEquiv
  rw [Category.assoc, ← η.naturality, ← Category.assoc]

/-- 概要：底変換の持ち上げは係数図式の自然変換と可換。
方針：二つの射影との合成を計算し、pullback の一意性を使う。
規約：二つの可換条件の証明は独立に指定する。
使われ方：Kerodon 5.3.3.1（Tag 025X） の相対単体の係数自然性。 -/
lemma weightedNerveBaseChangeLift_postcomp {C D : Type u} [Category.{u} C] [Category.{u} D]
    (K : D ⥤ C) {F G : C ⥤ SSet.{u}} (η : F ⟶ G) {T : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (b : T ⟶ nerve D)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = b ≫ nerveMap K)
    (hb : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G = b ≫ nerveMap K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift K G (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) b hb =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift K F a b ha ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (Functor.whiskerLeft K η) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseMap_isPullback K G).hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift_base, Category.assoc, weightedNerveBaseMap_postcomp,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift_base]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift_projection, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_projection,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift_projection]

/-- 概要：底の標準単体上の最後の係数評価は係数図式の自然変換と可換。
方針：底変換の持ち上げの自然性と終対象での評価の自然性を合成する。
規約：底の単体とパラメータに充填性を要求しない。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.4.6（Tag 03BB） の係数の持ち上げ問題への還元。 -/
lemma weightedNerveSimplexCoefficient_postcomp {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) {n : ℕ} (σ : ComposableArrows C n)
    {T : SSet.{u}} (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (b : T ⟶ (Δ[n] : SSet.{u}))
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = b ≫ SSet.yonedaEquiv.symm σ)
    (hb : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G =
      b ≫ SSet.yonedaEquiv.symm σ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient G σ (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) b hb =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a b ha ≫ η.app (σ.obj (Fin.last n)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient
  rw [weightedNerveBaseChangeLift_postcomp, Category.assoc,
    weightedNerveTerminalEvaluation_postcomp, ← Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
