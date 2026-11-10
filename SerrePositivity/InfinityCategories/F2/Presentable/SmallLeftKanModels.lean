module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallRightFibrationModels
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallCompactSourceSlices
public import SerrePositivity.InfinityCategories.F2.Presentable.CofinalColimitExistence
public import SerrePositivity.InfinityCategories.F1B.KanExtension.Shapes

/-!
概要：局所小さい圏への小さい始域の左 Kan 添字に小模型を与える。
方針：元の slice 射影を引き戻し、各写像空間の小模型から全空間を縮小する。
規約：元の左 Kan 添字の厳密な小ささを仮定しない。
使われ方：compact 模型に沿う標準密度余錐の存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：局所小さい圏への小さい始域の左 Kan 全添字は小模型を持つ。
方針：始域上の right fibration の fiber を元の小さい写像空間へ戻す。
規約：元の関手と指定頂点を保つ。
使われ方：左 Kan 局所余極限の小宇宙での構成。 -/
lemma exists_smallLeftKanShapeModel {A : SSet.{u}} [Quasicategory A]
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsLocallySmall C)
    (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C) (y : C _⦋0⦌) :
    ∃ (M : SSet.{u}) (hM : Quasicategory M), letI := hM
      Nonempty (QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj M) (leftKanShape i y)) := by
  let p := sliceOverProjection (SSet.yonedaEquiv.symm y)
  have : RightFibration (leftKanProjection i y) :=
    ⟨rightFibrations.pullback_fst i p RightFibration.mem⟩
  have : Quasicategory (leftKanShape i y) :=
    quasicategory_of_innerFibration (leftKanProjection i y)
  have (n : SimplexCategoryᵒᵖ) :
      Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj A).obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (A.obj n)))
  apply exists_smallRightFibrationModel_of_small_base (leftKanProjection i y)
  intro a
  have hs := hC.sliceOver_fiber_hasSmallKanModel (SSet.yonedaEquiv.symm y) (i.app _ a)
  exact hs.of_equivalence
    (qCatEquivalenceOfIso (vertexFiberIsoOfIsPullback (IsPullback.of_hasPullback i p).flip a)).symm

/-- 概要：小さい始域から局所小さい圏への左 Kan の局所余極限は余完備な標的で存在する。
方針：同値な小模型へ図式を制限して余極限を取り、全余錐の同値で戻す。
規約：大きい左 Kan 添字上の全小余極限を標的へ追加しない。
使われ方：compact 模型に沿う点ごとの左 Kan 延長の構成。 -/
lemma hasColimit_leftKanDiagram_of_locallySmall
    {A : SSet.{u}} [Quasicategory A]
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : IsLocallySmall C) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D)
    (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ D) (y : C _⦋0⦌) :
    HasColimit (leftKanDiagram i F y) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_smallLeftKanShapeModel hC i y
  have := hM
  exact hasColimit_of_fullyFaithfulPrecomposition e.hom
    (e.isQCatEquivalence.isPrecompositionEquivalence D).choose.isFullyFaithful
    (leftKanDiagram i F y) (hD M (e.hom ≫ leftKanDiagram i F y))

end SerrePositivity.InfinityCategories.F2.Presentable
