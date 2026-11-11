module

public import SerrePositivity.KST.NonConnective.SequentialLatchingHom

/-!
概要：相対 latching 射の Hom に対する一つの持ち上げから、次段の三つの境界を保つ族を得る。
方針：二つの既定部分を実引き戻しで貼り、指定した持ち上げ問題を解く。
規約：必要な一つの持ち上げ性を明示し、図式全体の fibration 性とは区別する。
使われ方：相対 cofibrant な BF 射の前合成のホーン充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 次段の既定の部分族・前段・元の源を全て保つ実際の Hom 族。 -/
lemma sequentialRelativeHomNext {X Z : OmegaSpectrum.{u}} (f : X ⟶ Z) (n : ℕ)
    (Y : PointedSimplicialSet.{u}) {A B : SSet.{u}} (j : A ⟶ B)
    [HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (sequentialRelativeLatchingMap f n) Y)]
    (a : A ⟶ (PointedObject.basedHom (Z.level (n + 1)).space Y).right)
    (u : B ⟶ (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (Z.level n).space) Y).right)
    (v : B ⟶ (PointedObject.basedHom (X.level (n + 1)).space Y).right)
    (huv : u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ f.app n) Y =
      v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) Y)
    (hu : j ≫ u = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (Z.sigma n) Y)
    (hv : j ≫ v = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f.app (n + 1)) Y) :
    ∃ l : B ⟶ (PointedObject.basedHom (Z.level (n + 1)).space Y).right,
      j ≫ l = a ∧ l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (Z.sigma n) Y = u ∧
        l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f.app (n + 1)) Y = v := by
  let hp := sequentialLatchingHom_isPullback f n Y
  let b := hp.lift u v huv
  have hleft : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
      (pushout.inl (PointedSimplicialSet.circle.{u} ◁ f.app n) (X.sigma n)) Y = u :=
    hp.lift_fst _ _ _
  have hright : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
      (pushout.inr (PointedSimplicialSet.circle.{u} ◁ f.app n) (X.sigma n)) Y = v :=
    hp.lift_snd _ _ _
  let sq : CommSq a j (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (sequentialRelativeLatchingMap f n) Y) b := ⟨by
    apply hp.hom_ext
    · simp only [Category.assoc, sequentialLatchingHom_pre_inl, hleft, hu]
    · simp only [Category.assoc, sequentialLatchingHom_pre_inr, hright, hv]⟩
  refine ⟨sq.lift, sq.fac_left, ?_, ?_⟩
  · rw [← sequentialLatchingHom_pre_inl f n Y, ← Category.assoc, sq.fac_right, hleft]
  · rw [← sequentialLatchingHom_pre_inr f n Y, ← Category.assoc, sq.fac_right, hright]

end SerrePositivity.KST.NonConnective
