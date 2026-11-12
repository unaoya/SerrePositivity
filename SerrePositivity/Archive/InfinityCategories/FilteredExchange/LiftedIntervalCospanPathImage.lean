module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransportAlgebra

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.LiftedIntervalCospanRectification
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanHomotopyRectificationImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.HomotopyIsoRawComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra

/-!
概要：厳密化した左脚の指定同型の共通点像を、元の持ち上げた全 path へ戻す。
方針：指定円柱の射影を計算し、共通点同型の往復を全円柱上で相殺する。
規約：同型の値を選び直さない。使われ方：元の模型比較の二脚の底の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits SSet
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.F2
variable {X Z : SSet.{u}} {E B : SSet.{max u v}} [KanComplex E] [KanComplex B]
  (f : X ⟶ Z) (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
  (s : (SSet.uliftFunctor.{v, u}).obj X ⟶ E)
  (t : (SSet.uliftFunctor.{v, u}).obj Z ⟶ B)
  (hs : (SSet.uliftFunctor.{v, u}).map f ≫ t = s ≫ p)

/-- 元の左脚の厳密化の指定像は、同じ持ち上げた指定円柱の類である。 -/
lemma liftedIntervalCospanLeftIso_image :
    HEq ((liftedIntervalCospanLeftIso f p s t hs).postcomp p)
      (functorIsoOfSimplicialHomotopy (liftedIntervalCospanHomotopy f p s t hs)) := by
  have h := kanHomotopyRectificationIso_image p
    ((SSet.uliftFunctor.{v, u}).map (pullback.snd ((intervalEndpointNatTrans 0).app Z) f) ≫ s)
    ((SSet.uliftFunctor.{v, u}).map (intervalReplacementEndpoint f) ≫ t)
    (liftedIntervalCospanHomotopy f p s t hs)
  exact (functorIsoOfEq_heq _ _ _).symm.trans (heq_of_eq h)

/-- 共通点の同型で後合成すると、元の小さい全 path を持ち上げた指定類を回収する。 -/
lemma liftedIntervalCospanLeftIso_commonImage [KanComplex Z]
    (I : B ≅ (SSet.uliftFunctor.{v, u}).obj Z)
    (hI : (SSet.uliftFunctor.{v, u}).map f ≫ I.inv = s ≫ p) :
    HEq (((liftedIntervalCospanLeftIso f p s I.inv hI).postcomp p).postcomp I.hom)
      (functorIsoOfSimplicialHomotopy (uliftSimplicialHomotopy.{u, v}
        (intervalReplacementPathHomotopy f (𝟙 _)))) := by
  let H := liftedIntervalCospanHomotopy f p s I.inv hI
  have hp := functorIso_postcomp_heq_of_heq (functorIsoOfSimplicialHomotopy H)
    ((liftedIntervalCospanLeftIso f p s I.inv hI).postcomp p) rfl
    (liftedIntervalCospanLeft_over f p s I.inv hI).symm
    (liftedIntervalCospanLeftIso_image f p s I.inv hI) I.hom
  refine hp.trans ((heq_of_eq (homotopyIso_postcomp H I.hom).symm).trans ?_)
  apply homotopyIso_heq_of_h_eq
  change (_ ≫ I.inv) ≫ I.hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.InfinityCategories.F2
