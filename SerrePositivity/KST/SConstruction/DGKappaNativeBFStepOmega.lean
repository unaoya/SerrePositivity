module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFPositiveStages
public import SerrePositivity.KST.SConstruction.StableKanAssemblyAdjoint
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderComponents

/-!
概要：有限 native BF の実次段の構造随伴に元の Ω 条件を証明する。
方針：元の組み立て随伴と同じ実円柱の基点固定四角形を使う。
規約：Ω 条件を帰納入力にしない。使われ方：同じ全四角形の実 BF スペクトル化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories
open NonConnective Spectra Spectra.PointedMapping SimplicialModel
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (r : ℕ)
  (S : DGKappaNativeBFFiniteStage.{u, v} R D I r)

local instance nativeFiniteStageKan (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex (S.functor.obj C).obj.right := S.kan C

local instance nativeFiniteStepKan (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex (((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj).right :=
  dgKappaNativeBFFiniteStep_kanComplex.{u, v} R D I r S C

local instance nativeFiniteBoundaryKan (n : ℕ) (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex (((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I n).obj C).obj).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _

local instance nativeFiniteStepLoopKan (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex ((ihom PointedSimplicialSet.circle.{max (u + 1) v}).obj
      ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj).right :=
  loopSpace_kanComplex _

local instance nativeFiniteAssemblySourceKan (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex (((coaugmentedPointedEnrichedFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit).obj ((stableOneDirectionPointedEnrichedFunctor r).obj
        ((dgKappaNativeBFFiniteInclusion.{u, v} R D I).obj C))).obj).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _

local instance nativeFiniteBoundaryLoopKan (n : ℕ)
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex ((ihom PointedSimplicialSet.circle.{max (u + 1) v}).obj
      ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I n).obj C).obj).right :=
  loopSpace_kanComplex _

/-- 概要：同じ前向き帰納比較は全基点 π 同型。
方針：元の Kan 値間の局所化可逆性を使う。
規約：同じ実比較を保持。使われ方：元の S₁ 比較との合成。 -/
lemma dgKappaNativeBFFiniteStageComparison_piIsomorphism
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (show ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C).obj ⟶
        (S.functor.obj C).obj from S.comparison C).right :=
  kanPiIsomorphism_of_localized_isIso _ (S.weak C)

/-- 概要：同じ実延長左脚は、元の二比較の合成の suspension。
方針：同じ円の左 tensor の合成保存を使う。
規約：同じ実左脚を保持。使われ方：実円柱の Ω 四角形への照合。 -/
lemma dgKappaNativeBFFiniteStepLeftMap_suspension
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (show ((dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r).obj C).obj ⟶
      ((dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S).obj C).obj from
        dgKappaNativeBFFiniteStepLeftMap.{u, v} R D I r S.functor S.comparison C) =
      PointedSimplicialSet.circle.{max (u + 1) v} ◁
        ((stableOneDirectionKanComparisonMap r C.obj).hom ≫
          (show ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C).obj ⟶
            (S.functor.obj C).obj from S.comparison C)) := by
  change (PointedSimplicialSet.circle.{max (u + 1) v} ◁
    (stableOneDirectionKanComparisonMap r C.obj).hom) ≫
      (PointedSimplicialSet.circle.{max (u + 1) v} ◁ _) = _
  exact (whiskerLeft_comp _ _ _).symm

/-- 概要：同じ実次段の構造随伴は全基点・全次数で π 同型。
方針：元の組み立て随伴と同じ実円柱の四角形に既存の Ω 判定を適用する。
規約：同じ実構造射を保持。使われ方：有限 native BF 全列の Ω 条件。 -/
lemma dgKappaNativeBFFiniteStepStructureAdjoint_piIsomorphism
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (curry
      (show _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (S.functor.obj C).obj ⟶
        ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj from
          dgKappaNativeBFFiniteStepStructureMap.{u, v} R D I r S C)).right := by
  let l : ((stableOneDirectionKanEnrichedFunctor r).obj C.obj).obj ⟶
      (S.functor.obj C).obj :=
    (stableOneDirectionKanComparisonMap r C.obj).hom ≫ S.comparison C
  let a : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (((stableOneDirectionKanEnrichedFunctor r).obj C.obj).obj) ⟶
      ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1)).obj C).obj :=
    dgKappaNativeBFFiniteAssemblyRightMap.{u, v} R D I r C
  let c : ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1)).obj C).obj ⟶
      ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj :=
    dgKappaNativeBFFiniteStepComparison.{u, v} R D I r S C
  have hl : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism l.right :=
    (stableOneDirectionKanComparisonMap_piIsomorphism r C.obj).comp
      (dgKappaNativeBFFiniteStageComparison_piIsomorphism.{u, v} R D I r S C)
  have ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (curry a).right :=
    stableKanAssemblyRightAdjoint_piIsomorphism r C.obj
  have hc : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism c.right := kanPiIsomorphism_of_localized_isIso _
    (dgKappaNativeBFFiniteStepComparison_localized_isIso.{u, v} R D I r S C)
  apply cylinderAssemblyAdjoint_piIsomorphism l hl a ha c hc
  let σ : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (S.functor.obj C).obj ⟶
      ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj :=
    dgKappaNativeBFFiniteStepStructureMap.{u, v} R D I r S C
  have h := pointedEnrichedCylinderCompletion_component_square
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1))
    (dgKappaNativeBFFiniteStepLeftMap.{u, v} R D I r S.functor S.comparison)
    (dgKappaNativeBFFiniteAssemblyRightMap.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeft_whisker.{u, v} R D I r
      S.functor S.comparison S.naturality)
    (dgKappaNativeBFFiniteAssemblyRight_whisker.{u, v} R D I r) C
  have he := congrArg (fun f => componentOf (f ≫ σ))
    (dgKappaNativeBFFiniteStepLeftMap_suspension.{u, v} R D I r S C)
  exact he.symm.trans h

end SerrePositivity.KST.SConstruction
