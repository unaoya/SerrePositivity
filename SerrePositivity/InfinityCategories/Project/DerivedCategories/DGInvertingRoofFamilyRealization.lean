module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGEvaluationSliceRealization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedRoofImageProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedDenominatorHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofPullbackHomotopy
/-!
概要：指定した実評価族を、任意標的の実屋根内の全パラメータ比較として実現する。
方針：評価方程式の実 slice ホモトピーと指定実分母の細分ホモトピーを pullback で組にする。
規約：指定評価族・全時刻の底・始点補正三角形を保持する。使われ方：全降下選択空間との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x y : D) {K Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
variable (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
variable (n : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) r.obj.left) y)
variable (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingPinchedFamilyEvaluation A D F r.obj.hom n)
/-- 指定評価族の実屋根内の比較。底と実 slice 比較の全時刻を保持する。 -/
structure DGInvertingRoofFamilyRealization where
  realization : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingPinchedSliceRealization A D F r.obj.hom n e
  homotopy : SSet.Homotopy
    ((n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y r) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F)
    (e.value ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
  target : homotopy.h ≫ pullback.fst _ _ = realization.homotopy.h
  projection : homotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F
    (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedDenominatorHomotopy A D P x r K).h
/-- 同じ実評価族に、元の指定閉分母と同じ全底を持つ実屋根比較が存在する。 -/
lemma dgInvertingRoofFamilyRealization_nonempty [Quasicategory Y] :
    Nonempty (DGInvertingRoofFamilyRealization A D P x y F r n e) := by
  obtain ⟨R⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingPinchedSliceRealization_nonempty A D F r.obj.hom n e
  let a := (n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y r) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F
  let b := e.value ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F
    (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm
    (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ F
  have ha : a ≫ pullback.fst p s =
      (n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) r.obj.left))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice Y _ _ := by
    dsimp only [a]
    rw [Category.assoc, Category.assoc, ← Category.assoc
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y r)]
    exact (congrArg (fun f => n ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofImage_target A D P x y r F)).trans
      (Category.assoc _ _ _).symm
  have hb : b ≫ pullback.fst p s = e.value ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice Y _ _ := by
    dsimp only [b]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_target]
    rfl
  have ha' : a ≫ pullback.snd p s =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x r) := by
    dsimp only [a]
    change ((n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y r) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F _ = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap_projection, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion_projection, SSet.comp_const]
  have hb' : b ≫ pullback.snd p s =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x) := by
    dsimp only [b]
    change (e.value ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F _) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F _ = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_projection, SSet.comp_const]
  let H := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget R.homotopy ha.symm hb.symm
  let J := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedDenominatorHomotopy A D P x r K) ha'.symm hb'.symm
  have h : H.h ≫ p = J.h ≫ s :=
    R.over.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedDenominatorHomotopy_source A D P x r K F).symm
  exact ⟨⟨R, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPullbackHomotopy p s H J h,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPullbackHomotopy_fst p s H J h, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPullbackHomotopy_snd p s H J h⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
