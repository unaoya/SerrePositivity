module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexCorrectedGlobalEndpoints
public import SerrePositivity.InfinityCategories.F1.PathCorrectedSquareGlobalTriangle

/-!
概要：元の二つの補正成分の指定像は、共有頂点で同じ直接自然性を回収する。
方針：補正 path の像を既存の両脚の三角等式へ貼り合わせる。
規約：元の全 Hom と補正 path の指定値を保持する。
使われ方：補正 pullback 比較と元の分類 Hom 作用の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 最初の補正成分と大域自然性の指定合成は、共有頂点で元の直接自然性を回収する。 -/
lemma cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_heq :
    HEq ((cocartesianTwoSimplexCorrectedFirstGlobalIso k p q).postcomp
      ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl))
      (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q) := by
  exact (cocartesianTwoSimplexCorrectedFirstSquare k p q).globalComposite_postcomp_heq
    (cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexFirstCell k) p q)
    (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexFirstCell k) p q)
    (cocartesianTwoSimplexSharedFirstNaturalityIso k p q)
    (cocartesianTwoSimplexSharedFirstGlobalNaturalityIso k p q)
    (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q)
    (cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_source k p q) rfl
    (cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_target k p q)
    (F2.functorIsoOfEq_heq
      (cocartesianOriginalCellOverNaturalityIso
        (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
        (cocartesianTwoSimplexFirstCell k) (cocartesianTwoSimplexSharedCell k) rfl p q)
      (cocartesianOriginalCellOverNaturality_source _ _ _ _ p q)
      (cocartesianOriginalCellOverNaturality_middle _ _ _ _ p q)).symm
    (F2.functorIsoOfEq_heq
      (cocartesianOriginalCellOverNaturalitySecondIso
        (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
        (cocartesianTwoSimplexFirstCell k) (cocartesianTwoSimplexSharedCell k) rfl p q)
      rfl (cocartesianOriginalCellOverNaturality_target _ _ _ _ p q)).symm
    (cocartesianTwoSimplexSharedFirstNaturality_triangle k p q)

/-- 次の補正成分と大域自然性の指定合成は、共有頂点で元の直接自然性を回収する。 -/
lemma cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_heq :
    HEq ((cocartesianTwoSimplexCorrectedSecondGlobalIso k p q).postcomp
      ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr))
      (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q) := by
  exact (cocartesianTwoSimplexCorrectedSecondSquare k p q).globalComposite_postcomp_heq
    (cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexSecondCell k) p q)
    (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSecondCell k) p q)
    (cocartesianTwoSimplexSharedSecondNaturalityIso k p q)
    (cocartesianTwoSimplexSharedSecondGlobalNaturalityIso k p q)
    (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q)
    (cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_source k p q) rfl
    (cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_target k p q)
    (F2.functorIsoOfEq_heq
      (cocartesianOriginalCellOverNaturalityIso
        (cocartesianSimplexCellIndex (SimplexCategory.δ (1 : Fin 2)))
        (cocartesianTwoSimplexSecondCell k) (cocartesianTwoSimplexSharedCell k) (cocartesianTwoSimplexSharedCell_second k) p q)
      (cocartesianOriginalCellOverNaturality_source _ _ _ _ p q)
      (cocartesianOriginalCellOverNaturality_middle _ _ _ _ p q)).symm
    (F2.functorIsoOfEq_heq
      (cocartesianOriginalCellOverNaturalitySecondIso
        (cocartesianSimplexCellIndex (SimplexCategory.δ (1 : Fin 2)))
        (cocartesianTwoSimplexSecondCell k) (cocartesianTwoSimplexSharedCell k) (cocartesianTwoSimplexSharedCell_second k) p q)
      rfl (cocartesianOriginalCellOverNaturality_target _ _ _ _ p q)).symm
    (cocartesianTwoSimplexSharedSecondNaturality_triangle k p q)

end SerrePositivity.InfinityCategories
