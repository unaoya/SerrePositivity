module

public import SerrePositivity.KST.NonConnective.SequentialRelativeCofibration
public import SerrePositivity.KST.NonConnective.SequentialHomStep
public import SerrePositivity.KST.Spectra.CofiberMappingPullback

/-!
概要：BF 射の相対 latching 対象への全 Hom は、二つの既定部分への Hom の引き戻し。
方針：既存の反変点つき内部 Hom 関手を元の押し出しへ適用する。
規約：全パラメータの実際の引き戻しであり、π の主張ではない。
使われ方：相対 cofibrant な射による前合成のホーン充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

variable {X Z : OmegaSpectrum.{u}} (f : X ⟶ Z) (n : ℕ) (Y : PointedSimplicialSet.{u})

/-- 相対 latching の Hom は、元の二つの部分への制限の引き戻し。 -/
lemma sequentialLatchingHom_isPullback :
    IsPullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pushout.inl (PointedSimplicialSet.circle.{u} ◁ f.app n) (X.sigma n)) Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pushout.inr (PointedSimplicialSet.circle.{u} ◁ f.app n) (X.sigma n)) Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ f.app n) Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) Y) := by
  have h := ((IsPushout.of_hasPushout (PointedSimplicialSet.circle.{u} ◁ f.app n)
    (X.sigma n)).op.flip).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor Y)
  simpa only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor_map] using h

/-- 制限を latching の左部分へ戻すと、元の標的の構造射による制限。 -/
lemma sequentialLatchingHom_pre_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (sequentialRelativeLatchingMap f n) Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pushout.inl (PointedSimplicialSet.circle.{u} ◁ f.app n) (X.sigma n)) Y =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (Z.sigma n) Y := by
  rw [← sequentialPointedPre_comp]
  exact congrArg (fun q ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre q Y) (pushout.inl_desc _ _ _)

/-- 制限を latching の右部分へ戻すと、元の BF 射の次段による制限。 -/
lemma sequentialLatchingHom_pre_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (sequentialRelativeLatchingMap f n) Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pushout.inr (PointedSimplicialSet.circle.{u} ◁ f.app n) (X.sigma n)) Y =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f.app (n + 1)) Y := by
  rw [← sequentialPointedPre_comp]
  exact congrArg (fun q ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre q Y) (pushout.inr_desc _ _ _)

end SerrePositivity.KST.NonConnective
