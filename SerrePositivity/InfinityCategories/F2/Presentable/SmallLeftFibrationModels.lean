module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.EssentiallySmallStraightening
public import SerrePositivity.InfinityCategories.F1.Universe.SmallFibration
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallFullModel
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1.Equivalences.EquivalenceLiftingPullback

/-!
概要：小さい底の模型と小さい Kan fiber を持つ left fibration の全空間を縮小する。
方針：小さい底へ引き戻し、分類図式の unstraightening を次数ごとに縮小する。
規約：元の全空間の単体の厳密な小ささや accessibility は仮定しない。
使われ方：compact 始域を持つ comma の小さい全同値模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：次数ごとに小さい底上の、小さい Kan fiber を持つ left fibration は小模型を持つ。
方針：coherent な分類による全空間比較と unstraightening の次数 fiber の小ささを使う。
規約：元の単体そのものは縮小せず、同値な全空間を縮小する。
使われ方：小さい底へ制限した comma の宇宙制御。 -/
lemma exists_smallLeftFibrationModel_of_small_base
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    [∀ n, Small.{u} (B.obj n)] (p : E ⟶ B) [LeftFibration p]
    (hp : HasEssentiallySmallFibers p) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A), letI := hA
      Nonempty (QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A) E) := by
  let F := essentiallySmallLeftStraighteningDiagram p hp
  have hs : HasSmallSimplexFibers (leftUnstraighteningProjection F) :=
    leftUnstraighteningProjection_hasSmallSimplexFibers F
  have (n : SimplexCategoryᵒᵖ) : Small.{u} ((leftUnstraightening F).obj n) :=
    hs.total_obj_small n
  let A := smallSimplicialSet.{u, u + 1} (leftUnstraightening F)
  let e := smallSimplicialSetIso.{u, u + 1} (leftUnstraightening F)
  have : InnerFibration e.hom := ⟨MorphismProperty.of_isIso innerFibrations _⟩
  have : Quasicategory ((SSet.uliftFunctor.{u + 1, u}).obj A) :=
    quasicategory_of_innerFibration e.hom
  have : Quasicategory A := quasicategory_of_ulift.{u, u + 1} A
  have hc : IsQCatEquivalence (essentiallySmallLeftStraighteningComparison p hp) :=
    (essentiallySmallLeftStraighteningComparison_isPrecompositionEquivalence p hp).isQCatEquivalence
  exact ⟨A, inferInstance, ⟨(qCatEquivalenceOfIso e).trans hc.choose.symm⟩⟩

/-- 概要：小さい模型を持つ底上の、小さい Kan fiber を持つ left fibration は小模型を持つ。
方針：指定した底の全同値で引き戻し、同値を持ち上げる射影に沿って全空間を戻す。
規約：元の底に次数ごとの小ささを追加しない。
使われ方：小 compact 全部分圏上の comma の縮小。 -/
lemma exists_smallLeftFibrationModel_of_base_model
    {K : SSet.{u}} [Quasicategory K]
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (hp : HasEssentiallySmallFibers p)
    (e : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj K) B) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A), letI := hA
      Nonempty (QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A) E) := by
  have : LeftFibration (pullback.snd p e.hom) :=
    ⟨leftFibrations.pullback_snd p e.hom LeftFibration.mem⟩
  have : Quasicategory (pullback p e.hom) :=
    quasicategory_of_innerFibration (pullback.snd p e.hom)
  have (n : SimplexCategoryᵒᵖ) :
      Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj K).obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (K.obj n)))
  obtain ⟨A, hA, ⟨a⟩⟩ := exists_smallLeftFibrationModel_of_small_base
    (pullback.snd p e.hom) (hp.pullback_snd e.hom)
  have := hA
  have he := e.isQCatEquivalence.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting
    p (leftFibration_equivalenceLifting p)
  have ht : IsQCatEquivalence (pullback.fst p e.hom) := by
    have h := (qCatEquivalenceOfIso (pullbackSymmetry p e.hom)).isQCatEquivalence.comp
      he.isQCatEquivalence
    change IsQCatEquivalence ((pullbackSymmetry p e.hom).hom ≫ pullback.snd e.hom p) at h
    simpa only [pullbackSymmetry_hom_comp_snd] using h
  exact ⟨A, hA, ⟨a.trans ht.choose⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
