module
public import SerrePositivity.InfinityCategories.Derived.DGEvaluationSliceRealization
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofImageProjections
public import SerrePositivity.InfinityCategories.Derived.DGClosedDenominatorHomotopy
public import SerrePositivity.InfinityCategories.Derived.RoofPullbackHomotopy
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) (x y : D) {K Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y)
variable (r : DGClosedVerdierDenominators A D P x)
variable (n : K ⟶ DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) r.obj.left) y)
variable (e : DGInvertingPinchedFamilyEvaluation A D F r.obj.hom n)
/-- 指定評価族の実屋根内の比較。底と実 slice 比較の全時刻を保持する。 -/
structure DGInvertingRoofFamilyRealization where
  realization : DGInvertingPinchedSliceRealization A D F r.obj.hom n e
  homotopy : SSet.Homotopy
    ((n ≫ dgClosedRoofHomInclusion A D P x y r) ≫ dgInvertingRoofFunctorMap A D P x y F)
    (e.value ≫ dgInvertingFixedHomRoofMap A D P x F
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
  target : homotopy.h ≫ pullback.fst _ _ = realization.homotopy.h
  projection : homotopy.h ≫ dgInvertingRoofProjection A D P x F
    (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) =
      (dgClosedDenominatorHomotopy A D P x r K).h
/-- 同じ実評価族に、元の指定閉分母と同じ全底を持つ実屋根比較が存在する。 -/
lemma dgInvertingRoofFamilyRealization_nonempty [Quasicategory Y] :
    Nonempty (DGInvertingRoofFamilyRealization A D P x y F r n e) := by
  obtain ⟨R⟩ := dgInvertingPinchedSliceRealization_nonempty A D F r.obj.hom n e
  let a := (n ≫ dgClosedRoofHomInclusion A D P x y r) ≫ dgInvertingRoofFunctorMap A D P x y F
  let b := e.value ≫ dgInvertingFixedHomRoofMap A D P x F
    (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y))
  let p := sliceOverProjection (SSet.yonedaEquiv.symm
    (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
  let s := dgVerdierOverSource A D P x ≫ F
  have ha : a ≫ pullback.fst p s =
      (n ≫ pinchedHomMap F (Simplex.vertex (ForgetEnrichment.to (Complex A) r.obj.left))
        (Simplex.vertex y)) ≫ pinchedFamilySlice Y _ _ := by
    dsimp only [a]
    rw [Category.assoc, Category.assoc, ← Category.assoc
      (dgClosedRoofHomInclusion A D P x y r)]
    exact (congrArg (fun f => n ≫ f) (dgClosedRoofImage_target A D P x y r F)).trans
      (Category.assoc _ _ _).symm
  have hb : b ≫ pullback.fst p s = e.value ≫ pinchedFamilySlice Y _ _ := by
    dsimp only [b]
    rw [Category.assoc, dgInvertingFixedHomRoofMap_target]
    rfl
  have ha' : a ≫ pullback.snd p s =
      SSet.const (dgClosedVerdierDenominatorVertex A D P x r) := by
    dsimp only [a]
    change ((n ≫ dgClosedRoofHomInclusion A D P x y r) ≫
      dgInvertingRoofFunctorMap A D P x y F) ≫ dgInvertingRoofProjection A D P x F _ = _
    rw [Category.assoc, dgInvertingRoofFunctorMap_projection, Category.assoc,
      dgClosedRoofHomInclusion_projection, SSet.comp_const]
  have hb' : b ≫ pullback.snd p s =
      SSet.const (dgVerdierOverIdentityVertex A D P x) := by
    dsimp only [b]
    change (e.value ≫ dgInvertingFixedHomRoofMap A D P x F _) ≫
      dgInvertingRoofProjection A D P x F _ = _
    rw [Category.assoc, dgInvertingFixedHomRoofMap_projection, SSet.comp_const]
  let H := stableHomotopyRetarget R.homotopy ha.symm hb.symm
  let J := stableHomotopyRetarget (dgClosedDenominatorHomotopy A D P x r K) ha'.symm hb'.symm
  have h : H.h ≫ p = J.h ≫ s :=
    R.over.trans (dgClosedDenominatorHomotopy_source A D P x r K F).symm
  exact ⟨⟨R, roofPullbackHomotopy p s H J h,
    roofPullbackHomotopy_fst p s H J h, roofPullbackHomotopy_snd p s H J h⟩⟩
end SerrePositivity.InfinityCategories
