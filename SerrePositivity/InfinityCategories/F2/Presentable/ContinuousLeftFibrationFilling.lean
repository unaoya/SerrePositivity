module

public import SerrePositivity.InfinityCategories.F2.Presentable.ContinuousLeftFibrationSequence
public import SerrePositivity.InfinityCategories.F2.Presentable.LeftHornCellExtension
public import SerrePositivity.InfinityCategories.Core.RightFibration

/-!
概要：連続な左ホーン付加の可算余極限の射影は left fibration である。
方針：底上の有限表示性でホーンを一段へ下ろし、次段のセルの充填を余極限へ送る。
規約：底の quasicategory 性も元の対象の充填性も仮定しない。
使われ方：一般の前層の compact 生成に用いる連続な left fibration 置換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 可算反復の次段の脚と単位の合成は元の段の脚である。 -/
lemma leftHornCellSequence_step_ι {B : SSet.{u}} (X : Over B) (j : ℕ) :
    (leftHornCellStepUnit B).app ((leftHornCellStage B j).obj X) ≫
      (colimit.ι (leftHornCellSequence B) (AsSmall.up.obj (j + 1))).app X =
        (colimit.ι (leftHornCellSequence B) (AsSmall.up.obj j)).app X := by
  have h := colimit.w (leftHornCellSequence B) (AsSmall.up.map (homOfLE (Nat.le_succ j)))
  change (Functor.ofSequence (leftHornCellStageMap B)).map
    (homOfLE (Nat.le_succ j)) ≫ _ = _ at h
  rw [Functor.ofSequence_map_homOfLE_succ] at h
  exact NatTrans.congr_app h X

/-- 底上の反復の余極限は、各指定左ホーンを底を保って充填する。 -/
lemma exists_continuousLeftFibrationReplacement_extension {B : SSet.{u}} (X : Over B)
    (h : LeftHornCellIndex B)
    (t : leftHornCellSource h ⟶ (continuousLeftFibrationReplacement B).obj X) :
    ∃ F : leftHornCellTarget h ⟶ (continuousLeftFibrationReplacement B).obj X,
      leftHornCellArrow h ≫ F = t := by
  have : IsFinitelyPresentable.{u} (leftHornCellSource h) :=
    finiteOver_isFinitelyPresentable (leftHornCellSource h).hom
  have hc := isColimitOfPreserves ((evaluation (Over B) (Over B)).obj X)
    (colimit.isColimit (leftHornCellSequence B))
  obtain ⟨j, s, hs⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc t
  obtain ⟨j⟩ := j
  change s ≫ (colimit.ι (leftHornCellSequence B) (AsSmall.up.obj j)).app X = t at hs
  let sj : leftHornCellSource h ⟶ (leftHornCellStage B j).obj X := s
  have hsj : sj ≫ (colimit.ι (leftHornCellSequence B) (AsSmall.up.obj j)).app X = t := hs
  obtain ⟨F, hF⟩ := exists_leftHornCellStep_extension h sj
  refine ⟨F ≫ (colimit.ι (leftHornCellSequence B) (AsSmall.up.obj (j + 1))).app X, ?_⟩
  rw [← Category.assoc, hF, Category.assoc, leftHornCellSequence_step_ι, hsj]

/-- 具体的な可算セル付加の余極限の射影は left fibration。 -/
instance continuousLeftFibrationReplacement_leftFibration {B : SSet.{u}} (X : Over B) :
    LeftFibration ((continuousLeftFibrationReplacement B).obj X).hom where
  mem := by
    intro A D i hi
    cases hi with
    | @intro n i hi =>
      constructor
      intro a b sq
      let h : LeftHornCellIndex B := ⟨n, ⟨⟨i, hi⟩, b⟩⟩
      let t : leftHornCellSource h ⟶ (continuousLeftFibrationReplacement B).obj X :=
        Over.homMk a sq.w
      obtain ⟨F, hF⟩ := exists_continuousLeftFibrationReplacement_extension X h t
      exact ⟨⟨{
        l := F.left
        fac_left := congrArg (fun k ↦ k.left) hF
        fac_right := F.w }⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
