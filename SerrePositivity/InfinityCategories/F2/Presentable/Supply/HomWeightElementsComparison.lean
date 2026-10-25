module

public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentablePresheafSliceComparison
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningInfinityReconstruction
public import SerrePositivity.InfinityCategories.F2.Compact.ClassificationTransport
public import SerrePositivity.InfinityCategories.F1B.Equivalences.QCatEquivalenceOpposite
public import SerrePositivity.InfinityCategories.F1B.KanExtension.Shapes
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafHomWeights
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafUnstraightening

/-!
概要：任意の関手の局所左 Kan 形状を、元の Hom 係数前層の元の圏へ比較する。
方針：slice 引き戻しの反転を分類し、実際の復元射を元の宇宙へ反転して戻す。
規約：元の A への射影を厳密に保つ比較射を構成する。
使われ方：P-12 の Yoneda 指定単位の局所普遍性を密度余極限で検査する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

local instance : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor

local instance {A C : SSet.{u}} [Quasicategory C] (F : A ⟶ C) (c : C _⦋0⦌) :
    RightFibration (leftKanProjection F c) :=
  ⟨rightFibrations.pullback_fst _ _ (RightFibration.mem (p :=
    sliceOverProjection (SSet.yonedaEquiv.symm c)))⟩

/-- 概要：元の Hom_C(F(-),c) を一つの元の空間値前層として固定する。
方針：同じ元の表現可能前層を F の反転で制限する。
規約：宇宙は元の A・C の宇宙。使われ方：局所左 Kan 形状の密度模型。 -/
def homWeightPresheaf {A C : SSet.{u}} [Quasicategory C] (F : A ⟶ C)
    (c : C _⦋0⦌) : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F) ≫ representablePresheafInfinity c

/-- 概要：局所左 Kan 射影の反転の分類は元の Hom 係数前層と同型。
方針：引き戻し正方形を反転し、分類の底変換と表現可能 slice 比較を合成する。
規約：元の局所形状の射影を使う。使われ方：小さい復元射の標的の指定。 -/
def homWeightLocalProjection_classificationIso
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    FunctorIso (leftStraighteningInfinityDiagram (SSet.opFunctor.map (leftKanProjection F c)))
      (homWeightPresheaf F c) := by
  let q := sliceOverProjection (SSet.yonedaEquiv.symm c)
  let k := SSet.opFunctor.map F
  let r := SSet.opFunctor.map q
  have hs := ((IsPullback.of_hasPullback F q).map SSet.opFunctor).flip
  have : LeftFibration (pullback.snd r k) :=
    ⟨leftFibrations.pullback_snd r k (LeftFibration.mem (p := r))⟩
  exact Compact.leftClassification_overIso (SSet.opFunctor.map (leftKanProjection F c))
    (pullback.snd r k) hs.isoPullback hs.isoPullback_hom_snd ≪≫
      (leftStraighteningInfinityDiagram_baseChangeIso r k).symm ≪≫
        ((representablePresheafInfinity_sliceIso c).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map k)).symm

/-- 概要：反転した局所形状から指定 Hom 前層の小さい left unstraightening への射。
方針：同じ分類の復元射と前層の分類同型に沿う小さい比較を合成する。
規約：底は A.op。使われ方：元の圏への比較を反転前の模型で固定する。 -/
def homWeightLocalOppositeComparison
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    (leftKanShape F c).op ⟶ smallLeftUnstraightening (homWeightPresheaf F c) :=
  leftStraighteningInfinityReconstruction (SSet.opFunctor.map (leftKanProjection F c)) ≫
    smallLeftUnstraighteningComparisonOfFunctorIso (homWeightLocalProjection_classificationIso F c)

/-- 概要：反転模型の比較は元の射影を厳密に保つ。
方針：復元と分類同型の小さい比較の射影則を合成する。
規約：底の射は恒等。使われ方：元の圏の比較の射影の回収。 -/
lemma homWeightLocalOppositeComparison_projection
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    homWeightLocalOppositeComparison F c ≫
      smallLeftUnstraighteningProjection (homWeightPresheaf F c) =
        SSet.opFunctor.map (leftKanProjection F c) := by
  rw [homWeightLocalOppositeComparison, Category.assoc,
    smallLeftUnstraighteningComparisonOfFunctorIso_projection,
    leftStraighteningInfinityReconstruction_projection]

/-- 概要：反転模型の比較は元の全空間上の前合成同値。
方針：復元と前層同型の二つの同値性を合成する。
規約：実際の比較射を保持する。使われ方：密度余極限の形状置換。 -/
lemma homWeightLocalOppositeComparison_isPrecompositionEquivalence
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    IsPrecompositionEquivalence (homWeightLocalOppositeComparison F c) :=
  (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence _).comp
    (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence _)

/-- 概要：元の局所左 Kan 形状から元の Hom 前層の元の圏への実比較。
方針：反転模型の比較を反転し、元の全空間の二重反転を戻す。
規約：元の小さい形状を使う。使われ方：同じ表現可能図式の密度表示。 -/
def homWeightLocalElementsComparison
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    leftKanShape F c ⟶ smallRightUnstraightening (homWeightPresheaf F c) :=
  (SSet.opFunctorCompOpFunctorIso.app (leftKanShape F c)).inv ≫
    SSet.opFunctor.map (homWeightLocalOppositeComparison F c)

/-- 概要：元の元の圏への比較は A への射影を厳密に保つ。
方針：反転前の射影則と二重反転の自然性を計算する。
規約：図式の同型への弱化は不要。使われ方：元の Yoneda 密度図式の制限。 -/
lemma homWeightLocalElementsComparison_projection
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    homWeightLocalElementsComparison F c ≫
      smallRightUnstraighteningProjection (homWeightPresheaf F c) = leftKanProjection F c := by
  unfold homWeightLocalElementsComparison smallRightUnstraighteningProjection
  calc
    _ = (SSet.opFunctorCompOpFunctorIso.app (leftKanShape F c)).inv ≫
        SSet.opFunctor.map (homWeightLocalOppositeComparison F c ≫
          smallLeftUnstraighteningProjection (homWeightPresheaf F c)) ≫
        (SSet.opFunctorCompOpFunctorIso.app A).hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (SSet.opFunctorCompOpFunctorIso.app (leftKanShape F c)).inv ≫
        SSet.opFunctor.map (SSet.opFunctor.map (leftKanProjection F c)) ≫
        (SSet.opFunctorCompOpFunctorIso.app A).hom := by
      rw [homWeightLocalOppositeComparison_projection]
    _ = (SSet.opFunctorCompOpFunctorIso.app (leftKanShape F c)).inv ≫
        (SSet.opFunctorCompOpFunctorIso.app (leftKanShape F c)).hom ≫
        leftKanProjection F c := by
      exact congrArg (fun t ↦
        (SSet.opFunctorCompOpFunctorIso.app (leftKanShape F c)).inv ≫ t)
        (SSet.opFunctorCompOpFunctorIso.hom.naturality (leftKanProjection F c))
    _ = leftKanProjection F c := by
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 概要：元の局所左 Kan 形状と元の Hom 前層の元の圏の実比較は前合成同値。
方針：反転前の同値を反転して二重反転の同型を合成する。
規約：小さい元の全空間の射を判定する。使われ方：密度余極限を局所 Kan 形状へ制限。 -/
lemma homWeightLocalElementsComparison_isPrecompositionEquivalence
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    IsPrecompositionEquivalence (homWeightLocalElementsComparison F c) := by
  have : Quasicategory (leftKanShape F c) :=
    quasicategory_of_innerFibration (leftKanProjection F c)
  exact (isPrecompositionEquivalence_of_iso
    (SSet.opFunctorCompOpFunctorIso.app (leftKanShape F c)).symm).comp
      (F1B.isQCatEquivalence_op
        (homWeightLocalOppositeComparison_isPrecompositionEquivalence F c).isQCatEquivalence
        |>.isPrecompositionEquivalence)

end SerrePositivity.InfinityCategories.F2.Presentable
