module

public import SerrePositivity.InfinityCategories.F1.Weighted.NerveJointComparison
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorSpaceCurrying

/-!
概要：全 strict Kan 図式の族に対する weighted nerve の coherent な復元単位。
方針：共同評価の関手同型を curry し、strict transport の実現を既存の straightening へ同定する。
規約：底と図式の族を同時に動かす一つの関手空間内の同型。
使われ方：Kerodon Corollary 5.6.0.6、一般の相対表現の延長へ進むための標準比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：像の包含を通る Kan 図式の実現は strict transport の像の実現と一致する。
方針：curry 前の共同評価の各 Hom を同じ混合 Hom へ戻す。
規約：二つの実現の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6、weighted nerve の単位の終点を既存の候補へ接続する。 -/
lemma strictTransportKanDiagramEnriched_realization (C : Type u) [Category.{u} C] :
    coherentNerveMap (strictTransportKanDiagramEnriched (C := C)) ≫ kanDiagramRealization C =
      strictTransportDiagramRealization C := by
  apply uncurry_injective
  rw [kanDiagramRealization, uncurry_natural_left, uncurry_curry,
    strictTransportDiagramRealization, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, F⟩
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro P
  have hij := SimplicialThickening.Path.le (P.obj 0)
  change (diagonalKanDiagramHom (kanDiagramSimplexBase σ.down)
    (F.comp SSet strictTransportKanDiagramEnriched) i j).app m P =
      (diagonalStrictDiagramHom (strictDiagramSimplexBase σ.down) F i j).app m P
  rw [diagonalKanDiagramHom_of_le _ _ i j hij,
    diagonalStrictDiagramHom_of_le _ _ i j hij]
  rfl

/-- 概要：weighted nerve 後の全図式としての実現は既存の coherent straightening。
方針：豊穣関手の合成の coherent nerve と像の実現の等式を使う。
規約：図式の coherent パラメーターの全次数を含む射の等式。
使われ方：Kerodon Corollary 5.6.0.6、標準単位の終点の同定。 -/
lemma weightedNerveTransportDiagramEnriched_realization (C : Type u) [Category.{u} C] :
    coherentNerveMap (weightedNerveTransportDiagramEnriched C) ≫ kanDiagramRealization C =
      weightedNerveInfinityMap C ≫ leftStraighteningCoherentMap C := by
  rw [weightedNerveTransportDiagramEnriched, coherentNerveMap_comp,
    coherentNerveMap_comp, Category.assoc, Category.assoc,
    strictTransportKanDiagramEnriched_realization]
  change weightedNerveInfinityMap C ≫
    leftStrictTransportInfinityMap C ≫ strictTransportDiagramRealization C = _
  rw [leftStrictTransportInfinityMap_realization]

/-- 概要：全 strict Kan 図式の実現と weighted nerve の straightening は大域的に関手同型。
方針：実際の共同比較の可逆な辺を curry し、終点の実現を同定する。
規約：値ごとの同型の集まりではなく、関手空間に値を取る二写像の同型。
使われ方：Kerodon Corollary 5.6.0.6、strict な表現における全パラメーターの復元単位。 -/
noncomputable def weightedNerveStraighteningCoherentUnitIso (C : Type u) [Category.{u} C] :
    FunctorIso (kanDiagramRealization C)
      (weightedNerveInfinityMap C ≫ leftStraighteningCoherentMap C) := by
  have h := (weightedNerveJointComparisonIso C).curry
  change FunctorIso (curry (kanDiagramJointEvaluation C))
    (curry (_ ◁ coherentNerveMap (weightedNerveTransportDiagramEnriched C) ≫
      kanDiagramJointEvaluation C)) at h
  rw [curry_natural_left] at h
  change FunctorIso (kanDiagramRealization C)
    (coherentNerveMap (weightedNerveTransportDiagramEnriched C) ≫ kanDiagramRealization C) at h
  rw [weightedNerveTransportDiagramEnriched_realization] at h
  exact h

/-- 概要：任意の coherent な strict 図式の族は weighted nerve から大域的に復元される。
方針：標準単位の関手同型をパラメーター空間の射で引き戻す。
規約：底全体で比較し、パラメーター空間の quasicategory 性を要求しない。
使われ方：Kerodon §5.6.5、境界上で既に与えられた strict な族との比較。 -/
noncomputable def weightedNerveStraighteningCoherentFamilyUnitIso
    {C : Type u} [Category.{u} C] {B : SSet.{u + 1}} (A : B ⟶ KanDiagramNerve C) :
    FunctorIso (A ≫ kanDiagramRealization C)
      (A ≫ weightedNerveInfinityMap C ≫ leftStraighteningCoherentMap C) :=
  (weightedNerveStraighteningCoherentUnitIso C).precomp A

end SerrePositivity.InfinityCategories
