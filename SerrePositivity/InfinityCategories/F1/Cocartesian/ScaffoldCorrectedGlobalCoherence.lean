module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldCorrectedGlobalEndpoints
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

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 最初の補正成分と大域自然性の指定合成は、共有頂点で元の直接自然性を回収する。 -/
lemma cocartesianScaffoldCorrectedFirstGlobalIso_shared_heq :
    HEq ((cocartesianScaffoldCorrectedFirstGlobalIso n k p q).postcomp
      ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl))
      (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q) := by
  exact (cocartesianScaffoldCorrectedFirstSquare n k p q).globalComposite_postcomp_heq
    (cocartesianSingleBaseChangeHomAction (cocartesianScaffoldFirstCell n k) p q)
    (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldFirstCell n k) p q)
    (cocartesianScaffoldSharedFirstNaturalityIso n k p q)
    (cocartesianScaffoldSharedFirstGlobalNaturalityIso n k p q)
    (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q)
    (cocartesianScaffoldCorrectedFirstGlobalIso_shared_source n k p q) rfl
    (cocartesianScaffoldCorrectedFirstGlobalIso_shared_target n k p q)
    (F2.functorIsoOfEq_heq
      (cocartesianOriginalCellOverNaturalityIso
        (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
        (cocartesianScaffoldFirstCell n k) (cocartesianScaffoldSharedCell n k) rfl p q)
      (cocartesianOriginalCellOverNaturality_source _ _ _ _ p q)
      (cocartesianOriginalCellOverNaturality_middle _ _ _ _ p q)).symm
    (F2.functorIsoOfEq_heq
      (cocartesianOriginalCellOverNaturalitySecondIso
        (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
        (cocartesianScaffoldFirstCell n k) (cocartesianScaffoldSharedCell n k) rfl p q)
      rfl (cocartesianOriginalCellOverNaturality_target _ _ _ _ p q)).symm
    (cocartesianScaffoldSharedFirstNaturality_triangle n k p q)

/-- 次の補正成分と大域自然性の指定合成は、共有頂点で元の直接自然性を回収する。 -/
lemma cocartesianScaffoldCorrectedSecondGlobalIso_shared_heq :
    HEq ((cocartesianScaffoldCorrectedSecondGlobalIso n k p q).postcomp
      ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr))
      (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q) := by
  exact (cocartesianScaffoldCorrectedSecondSquare n k p q).globalComposite_postcomp_heq
    (cocartesianSingleBaseChangeHomAction (cocartesianScaffoldTailCell n k) p q)
    (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldTailCell n k) p q)
    (cocartesianScaffoldSharedSecondNaturalityIso n k p q)
    (cocartesianScaffoldSharedSecondGlobalNaturalityIso n k p q)
    (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q)
    (cocartesianScaffoldCorrectedSecondGlobalIso_shared_source n k p q) rfl
    (cocartesianScaffoldCorrectedSecondGlobalIso_shared_target n k p q)
    (F2.functorIsoOfEq_heq
      (cocartesianOriginalCellOverNaturalityIso
        (scaffoldFiniteZeroVertex n)
        (cocartesianScaffoldTailCell n k) (cocartesianScaffoldSharedCell n k) (cocartesianScaffoldSharedCell_tail n k) p q)
      (cocartesianOriginalCellOverNaturality_source _ _ _ _ p q)
      (cocartesianOriginalCellOverNaturality_middle _ _ _ _ p q)).symm
    (F2.functorIsoOfEq_heq
      (cocartesianOriginalCellOverNaturalitySecondIso
        (scaffoldFiniteZeroVertex n)
        (cocartesianScaffoldTailCell n k) (cocartesianScaffoldSharedCell n k) (cocartesianScaffoldSharedCell_tail n k) p q)
      rfl (cocartesianOriginalCellOverNaturality_target _ _ _ _ p q)).symm
    (cocartesianScaffoldSharedSecondNaturality_triangle n k p q)

end SerrePositivity.InfinityCategories
