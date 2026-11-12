module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveSimplexCoefficient

/-!
概要：weighted nerve の底変換の持ち上げと最後の係数評価のパラメータ自然性。
方針：pullback の一意性で持ち上げの前合成を計算し、終対象評価との合成へ移す。
規約：可換性の証明の選択は等式に影響しない。
使われ方：Kerodon §5.3.3（Tag 025W）、ホーンの係数充填を各面上で比較する計算。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：相対図式と底の図式が等しければ、その最後の係数評価も等しい。
方針：二つの図式の等式を消去し、可換性の証明の違いを証明無関係性で除く。
規約：同じ底の射列 σ と同じパラメータ T を使う。
使われ方：Kerodon §5.3.3（Tag 025W）、ホーン面を Yoneda の標準表示に直して評価する式。 -/
lemma weightedNerveSimplexCoefficient_congr {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C n) {T : SSet.{u}}
    (a a' : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (b b' : T ⟶ (Δ[n] : SSet.{u}))
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = b ≫ SSet.yonedaEquiv.symm σ)
    (h' : a' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = b' ≫ SSet.yonedaEquiv.symm σ)
    (ha : a = a') (hb : b = b') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a b h = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a' b' h' := by
  cases ha
  cases hb
  rfl

/-- 概要：weighted nerve の底変換の持ち上げはパラメータの前合成と可換。
方針：二つの射影の計算則と pullback の一意性を使う。
規約：可換性の証明 h と hr は独立に指定してよい。
使われ方：Kerodon §5.3.3（Tag 025W）、底の単体上への持ち上げをホーン面で制限する式。 -/
lemma weightedNerveBaseChangeLift_precomp {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) {T U : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (b : T ⟶ nerve D)
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = b ≫ nerveMap H) (r : U ⟶ T)
    (hr : (r ≫ a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (r ≫ b) ≫ nerveMap H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift H F (r ≫ a) (r ≫ b) hr =
      r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift H F a b h := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseMap_isPullback H F).hom_ext
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift_base]
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift_projection]

/-- 概要：底の標準単体上の最後の係数評価はパラメータの前合成と可換。
方針：底変換の持ち上げの自然性に終対象評価を後合成する。
規約：底の射列 σ は全パラメータで共通。
使われ方：Kerodon §5.3.3（Tag 025W）、係数ホーンの各面を元の重み付き図式から回収する式。 -/
lemma weightedNerveSimplexCoefficient_precomp {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C n) {T U : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (b : T ⟶ (Δ[n] : SSet.{u}))
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = b ≫ SSet.yonedaEquiv.symm σ) (r : U ⟶ T)
    (hr : (r ≫ a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (r ≫ b) ≫ SSet.yonedaEquiv.symm σ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ (r ≫ a) (r ≫ b) hr =
      r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a b h := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient
  simp only [Category.assoc]
  rw [weightedNerveBaseChangeLift_precomp, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
