module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransportDiagramRealization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.StrictTransportEnriched

/-!
概要：strict transport の像の実現と既存の coherent straightening の比較。
方針：相対 Hom の混合評価と strict な変換の混合評価を各次数で同定する。
規約：比較は選択した同値を挟まず、構成した写像そのものの等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、straightening を strict transport の像を経由して分解する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：strict transport の像での対角評価は元の相対 Hom の対角評価に一致する。
方針：各対象を定義で同定し、各 Hom の順向きの式を比較する。
規約：底の図式 A と coherent な fibration の図式は同じ順序 J を用いる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、全次数での実現の比較。 -/
lemma diagonalCocartesianTransportDiagramEvaluation_transport
    {C J : Type u} [Category.{u} C] [LinearOrder J] (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianTransportDiagramEvaluation A (F.comp SSet
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportCoreEnriched) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianSectionsEvaluation (A.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.underNerveDiagram C) F := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  have hij : i.as ≤ j.as := SimplicialThickening.Path.le (P.obj 0)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianTransportDiagramHom A (F.comp SSet
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportCoreEnriched) i j).app n P =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianSectionsHom (A.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.underNerveDiagram C) F i j).app n P
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianTransportDiagramHom_of_le A (F.comp SSet
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportCoreEnriched) i j hij,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianSectionsHom_of_le (A.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.underNerveDiagram C) F i j hij]
  rfl

/-- 概要：既存の straightening の共同評価は strict transport の像の共同評価を経由する。
方針：各単体で対角評価の比較を適用する。
規約：底の因子には恒等写像を作用させる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、curry 前の分解等式。 -/
lemma cocartesianTransportDiagramJointEvaluation_transport (C : Type u) [Category.{u} C] :
    (𝟙 _ ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportInfinityMap C) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramJointEvaluation
      C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportJointEvaluation C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, F⟩
  exact diagonalCocartesianTransportDiagramEvaluation_transport (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramSimplexBase σ.down) F

/-- 概要：coherent straightening は strict transport の像への比較とその実現の合成。
方針：uncurry の単射性で共同評価の分解等式へ帰着する。
規約：同値性はこの等式からは結論しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類問題を像の実現写像の性質へ移す。 -/
lemma cocartesianStrictTransportInfinityMap_realization (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramRealization C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap C := by
  apply uncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramRealization, uncurry_natural_left, uncurry_curry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap_uncurry]
  exact cocartesianTransportDiagramJointEvaluation_transport C

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
