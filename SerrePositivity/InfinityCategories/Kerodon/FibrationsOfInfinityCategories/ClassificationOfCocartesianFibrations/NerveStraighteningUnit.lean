module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveJointComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying

/-!
概要：全 strict Kan 図式の族に対する weighted nerve の coherent な復元単位。
方針：共同評価の関手同型を curry し、strict transport の実現を既存の straightening へ同定する。
規約：底と図式の族を同時に動かす一つの関手空間内の同型。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一般の相対表現の延長へ進むための標準比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：像の包含を通る Kan 図式の実現は strict transport の像の実現と一致する。
方針：curry 前の共同評価の各 Hom を同じ混合 Hom へ戻す。
規約：二つの実現の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、weighted nerve の単位の終点を既存の候補へ接続する。 -/
lemma strictTransportKanDiagramEnriched_realization (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportKanDiagramEnriched (C := C)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportDiagramRealization C := by
  apply uncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization, uncurry_natural_left, uncurry_curry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportDiagramRealization, uncurry_curry]
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
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase σ.down)
    (F.comp SSet _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportKanDiagramEnriched) i j).app m P =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalStrictDiagramHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramSimplexBase σ.down) F i j).app m P
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalStrictDiagramHom_of_le _ _ i j hij]
  rfl

/-- 概要：weighted nerve 後の全図式としての実現は既存の coherent straightening。
方針：豊穣関手の合成の coherent nerve と像の実現の等式を使う。
規約：図式の coherent パラメーターの全次数を含む射の等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、標準単位の終点の同定。 -/
lemma weightedNerveTransportDiagramEnriched_realization (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportDiagramEnriched C) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap C := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportDiagramEnriched, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, Category.assoc, Category.assoc,
    strictTransportKanDiagramEnriched_realization]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveInfinityMap C ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportDiagramRealization C = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportInfinityMap_realization]

/-- 概要：全 strict Kan 図式の実現と weighted nerve の straightening は大域的に関手同型。
方針：実際の共同比較の可逆な辺を curry し、終点の実現を同定する。
規約：値ごとの同型の集まりではなく、関手空間に値を取る二写像の同型。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な表現における全パラメーターの復元単位。 -/
noncomputable def weightedNerveStraighteningCoherentUnitIso (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap C) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveJointComparisonIso C).curry
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramJointEvaluation C))
    (curry (_ ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportDiagramEnriched C) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramJointEvaluation C)) at h
  rw [curry_natural_left] at h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportDiagramEnriched C) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization C) at h
  rw [weightedNerveTransportDiagramEnriched_realization] at h
  exact h

/-- 概要：任意の coherent な strict 図式の族は weighted nerve から大域的に復元される。
方針：標準単位の関手同型をパラメーター空間の射で引き戻す。
規約：底全体で比較し、パラメーター空間の quasicategory 性を要求しない。
使われ方：Kerodon §5.6.5（Tag 028U）、境界上で既に与えられた strict な族との比較。 -/
noncomputable def weightedNerveStraighteningCoherentFamilyUnitIso
    {C : Type u} [Category.{u} C] {B : SSet.{u + 1}} (A : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization C)
      (A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap C) :=
  (weightedNerveStraighteningCoherentUnitIso C).precomp A

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
