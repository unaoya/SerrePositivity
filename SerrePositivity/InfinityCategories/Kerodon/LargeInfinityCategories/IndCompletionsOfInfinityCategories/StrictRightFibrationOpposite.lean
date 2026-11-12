module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseOrdinaryKanImage
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RightFibrationOppositeComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentUnderlyingHo

/-!
概要：通常の right fibration 図式の反転は、共通 Hom 解像の同じ豊穣反転の制限。
方針：定値な通常の Hom の標準持ち上げと反転した射影・底上の射を照合する。
規約：一般の coherent な反転を、素朴な豊穣反転として定義し直さない。
使われ方：strict な余錐と right straightening の評価比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 通常の底上の射を反転する、固定した反対底への関手。 -/
def rightFibrationOppositeOrdinary (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B.op where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibrationOppositeObject
  map f := Over.homMk (SSet.opFunctor.map f.left) (by
    change SSet.opFunctor.map f.left ≫ SSet.opFunctor.map _ = SSet.opFunctor.map _
    rw [← CategoryTheory.Functor.map_comp, Over.w])
  map_id p := by
    apply Over.OverMorphism.ext
    exact SSet.opFunctor.map_id p.val.left
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact SSet.opFunctor.map_comp f.left g.left

/-- 同じ通常の反転は、標準持ち上げ後の豊穣反転の通常の作用と厳密に一致する。 -/
lemma edgewiseOrdinaryLift_rightFibrationOpposite (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOrdinaryLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibrationOppositeEnriched B) =
        rightFibrationOppositeOrdinary B := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro p q f
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibrationOppositeEnriched B)).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOrdinaryHom f) = (rightFibrationOppositeOrdinary B).map f
  apply (eHomEquiv SSet).injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedUnderlying_eHom_map]
  change eHomEquiv SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOrdinaryHom f) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRelativeFunctorOpposite q.val.hom p.val.hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv _ _ ((rightFibrationOppositeOrdinary B).map f)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRelativeFunctorOpposite_ι]
  refine Eq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv_ι
    ((rightFibrationOppositeOrdinary B).map f)).symm
  apply MonoidalClosed.uncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
