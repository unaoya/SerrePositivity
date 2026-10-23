module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteRelativeOverHom
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationCoherentEvaluation
public import SerrePositivity.InfinityCategories.F2.Ind.StrictCoconePostcomposition
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredKanCocone
public import SerrePositivity.InfinityCategories.F2.CoconeValEquality
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationCocone

/-!
概要：有限始域の相対 Hom は、底上の strict filtered 全余錐を native な空間の余極限へ写す。
方針：豊穣作用の通常の射への制限を元の相対後合成と同定し、全 join 射の等式で保存を戻す。
規約：元の全脚と全高次単体を保持する。一般の coherent 添字の保存は別に証明する。
使われ方：left fibrations の filtered 全表示の native な普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- left fibration の元の底上の対象と全ての通常の射を忘却する。 -/
def leftFibrationObjectForget (B : SSet.{u}) : LeftFibrationObject B ⥤ Over B where
  obj X := X.val
  map f := f

/-- 元の相対 Hom の Kan 値の通常の関手。 -/
def relativeLeftFibrationHomFunctor {B : SSet.{u}} (A : Over B) :
    LeftFibrationObject B ⥤ KanObject.{u} where
  obj X := (relativeFunctorEnrichedEvaluation A).obj X
  map f := (relativeOverHomFunctor A).map f
  map_id X := (relativeOverHomFunctor A).map_id X.val
  map_comp f g := (relativeOverHomFunctor A).map_comp f g

/-- 相対 Hom の全豊穣作用の通常の作用は、元の相対後合成と一致する。 -/
lemma relativeFunctorEnrichedEvaluation_underlying {B : SSet.{u}} (A : Over B) :
    coherentEnrichedUnderlyingFunctor (relativeFunctorEnrichedEvaluation A) =
      relativeLeftFibrationHomFunctor A := by
  refine CategoryTheory.Functor.ext
    (F := coherentEnrichedUnderlyingFunctor (relativeFunctorEnrichedEvaluation A))
    (G := relativeLeftFibrationHomFunctor A) (fun _ ↦ rfl) ?_
  intro X Y f
  change (coherentEnrichedUnderlyingFunctor (relativeFunctorEnrichedEvaluation A)).map f =
    (relativeLeftFibrationHomFunctor A).map f
  apply (SimplicialCategory.homEquiv'
    ((relativeFunctorEnrichedEvaluation A).obj X)
    ((relativeFunctorEnrichedEvaluation A).obj Y)).injective
  rw [coherentEnrichedUnderlyingFunctor_vertex]
  exact relativeFunctorPostHom_vertex A X.val Y.val f

/-- 相対 Hom の像の全余錐は、元の通常の相対 Hom 余錐と全 join 射で一致する。 -/
lemma relativeHom_strictCocone_postcomp_val {B : SSet.{u}} (A : Over B)
    {J : Type u} [SmallCategory J] {F : J ⥤ LeftFibrationObject B} (c : Cocone F) :
    (strictNativeCocone c).val ≫ leftFibrationCoherentEvaluation A =
      (strictNativeCocone ((relativeLeftFibrationHomFunctor A).mapCocone c)).val := by
  rw [leftFibrationCoherentEvaluation, Ind.strictNativeCocone_postcomp_val,
    relativeFunctorEnrichedEvaluation_underlying]

/-- 有限始域の元の相対 Hom は、指定した strict filtered 全余錐を空間の native な余極限へ写す。 -/
lemma finiteRelativeHom_preserves_strictCocone {B : SSet.{u}} (A : Over B) [A.left.Finite]
    {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ LeftFibrationObject B}
    (c : Cocone F) (hc : IsColimit ((leftFibrationObjectForget B).mapCocone c)) :
    IsColimitCone (mapJoinCocone (leftFibrationCoherentEvaluation A) (strictNativeCocone c)) := by
  apply (isColimitCone_iff_of_cocone_val_eq _ _ (relativeHom_strictCocone_postcomp_val A c)).mpr
  apply Ind.strictNativeCocone_isColimit_of_filtered_forget
  change IsColimit ((relativeOverHomFunctor A).mapCocone
    ((leftFibrationObjectForget B).mapCocone c))
  exact isColimitOfPreserves (relativeOverHomFunctor A) hc

end SerrePositivity.InfinityCategories.F2.Presentable
