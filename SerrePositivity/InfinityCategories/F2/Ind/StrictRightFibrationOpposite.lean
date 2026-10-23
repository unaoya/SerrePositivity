module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseOrdinaryKanImage
public import SerrePositivity.InfinityCategories.F1.Fibrations.RightFibrationOppositeComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentUnderlyingHo

/-!
概要：通常の right fibration 図式の反転は、共通 Hom 解像の同じ豊穣反転の制限。
方針：定値な通常の Hom の標準持ち上げと反転した射影・底上の射を照合する。
規約：一般の coherent な反転を、素朴な豊穣反転として定義し直さない。
使われ方：strict な余錐と right straightening の評価比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 通常の底上の射を反転する、固定した反対底への関手。 -/
def rightFibrationOppositeOrdinary (B : SSet.{u}) :
    RightFibrationObject B ⥤ LeftFibrationObject B.op where
  obj := rightFibrationOppositeObject
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
    edgewiseOrdinaryLift (RightFibrationObject B) ⋙
      coherentEnrichedUnderlyingFunctor (rightFibrationOppositeEnriched B) =
        rightFibrationOppositeOrdinary B := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro p q f
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change (coherentEnrichedUnderlyingFunctor (rightFibrationOppositeEnriched B)).map
    (edgewiseOrdinaryHom f) = (rightFibrationOppositeOrdinary B).map f
  apply (eHomEquiv SSet).injective
  rw [HomotopyLimits.enrichedUnderlying_eHom_map]
  change eHomEquiv SSet (edgewiseOrdinaryHom f) ≫
    edgewiseRelativeFunctorOpposite q.val.hom p.val.hom =
    relativeFunctorHomEquiv _ _ ((rightFibrationOppositeOrdinary B).map f)
  apply vertexFiber_hom_ext
  rw [Category.assoc, edgewiseRelativeFunctorOpposite_ι]
  refine Eq.trans ?_ (relativeFunctorHomEquiv_ι
    ((rightFibrationOppositeOrdinary B).map f)).symm
  apply MonoidalClosed.uncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
