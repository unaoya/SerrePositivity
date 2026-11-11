module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCoefficientFormula
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCoefficientNaturality

/-!
概要：weighted nerve の最後の係数評価は、元の係数自然変換と可換。
方針：底変換の持ち上げの一意性と、終対象評価の自然性を使う。
規約：係数の Kan 性を要求しない。使われ方：相対右端比較の weighted 境界充填。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I J : Type u} [Category.{u} I] [Category.{u} J]
  {F G : I ⥤ SSet.{u}} (η : F ⟶ G)

/-- 同じ係数自然変換と通常の底変換は weighted nerve 上で厳密に可換。 -/
lemma weightedBaseMap_coefficient_naturality (H : J ⥤ I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (Functor.whiskerLeft H η) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseMap H G =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseMap H F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η := rfl

/-- 終対象への評価は、元の係数自然変換と可換。 -/
lemma weightedTerminalEvaluation_coefficient_naturality {t : I} (ht : IsTerminal t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveTerminalEvaluation G ht =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveTerminalEvaluation F ht ≫ η.app t := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv ((s.2.app (Fin.last n) ≫ η.app _) ≫ G.map _) =
    (η.app t).app _ (SSet.yonedaEquiv (s.2.app (Fin.last n) ≫ F.map _))
  rw [← SSet.yonedaEquiv_comp]
  apply congrArg SSet.yonedaEquiv
  rw [Category.assoc, ← η.naturality, ← Category.assoc]
  rfl

/-- 同じ底変換の持ち上げは、元の係数自然変換の作用を保つ。 -/
lemma weightedBaseChangeLift_coefficient_naturality (H : J ⥤ I) {T : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (b : T ⟶ nerve J)
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = b ≫ nerveMap H)
    (h' : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G = b ≫ nerveMap H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift H F a b h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (Functor.whiskerLeft H η) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift H G (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) b h' := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseMap_isPullback H G).hom_ext
  · rw [Category.assoc, weightedBaseMap_coefficient_naturality, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift_base, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift_base]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_projection,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift_projection]

/-- 最後の係数評価は、任意のパラメータ上で元の自然変換と厳密に可換。 -/
lemma weightedSimplexCoefficient_map {n : ℕ} (σ : ComposableArrows I n) {T : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (b : T ⟶ (Δ[n] : SSet.{u}))
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = b ≫ SSet.yonedaEquiv.symm σ)
    (h' : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G =
      b ≫ SSet.yonedaEquiv.symm σ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a b h ≫ η.app (σ.obj (Fin.last n)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient G σ (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) b h' := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient
  have he := weightedTerminalEvaluation_coefficient_naturality
    (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexFunctor σ) η)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexTerminal.{u} n)
  rw [Category.assoc]
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexFunctor σ) F a
        (b ≫ (stdSimplex.isoNerve.{u} n).hom) _ ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexFunctor σ) η) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveTerminalEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexFunctor σ ⋙ G)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexTerminal.{u} n)) :=
      congrArg (fun q ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexFunctor σ)
        F a (b ≫ (stdSimplex.isoNerve.{u} n).hom) _ ≫ q) he.symm
    _ = _ := by
      rw [← Category.assoc, weightedBaseChangeLift_coefficient_naturality]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
