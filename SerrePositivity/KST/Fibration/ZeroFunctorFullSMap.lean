module
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSCoreFamily
public import SerrePositivity.KST.Fibration.ZeroTargetFullSMap

/-!
概要：元の零値完全関手を、全 S• から core S• への同じ実射として保持する。
方針：零図式への元の後合成を core へ持ち上げ、包含の単射性で全単体的自然性を反映する。
規約：始域を core に縮めず、元の指定関手を選び直さない。
使われ方：元の商核上辺と指定 Verdier 上側合成の全 S• 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 同じ零値完全関手の元の S_n 後合成を core S_n へ持ち上げる。 -/
def zeroFunctorSCoreMap {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) (n : ℕ) :
    sConstruction n A.obj ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C.obj) : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift (sExactMap n F).hom
    (map_edge_invertible_of_zero _ (zeroFunctor_sExactMap_values F hF n))

/-- core 包含後は、同じ元の完全関手による全 S_n 後合成そのもの。 -/
theorem zeroFunctorSCoreMap_ι {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) (n : ℕ) :
    zeroFunctorSCoreMap F hF n ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C.obj)).ι =
      (sExactMap n F).hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift_ι _ _

/-- 同じ全 S_n の零値作用は全ての面・退化に自然。 -/
def zeroFunctorFullSMap {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    simplicialSConstruction A.obj ⟶ simplicialSConstruction C.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor where
  app n := zeroFunctorSCoreMap F hF n.unop.len
  naturality {n m} θ := by
    change sMap A.obj θ.unop.toOrderHom ≫ zeroFunctorSCoreMap F hF m.unop.len =
      zeroFunctorSCoreMap F hF n.unop.len ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sMap C.obj θ.unop.toOrderHom)
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction _ C.obj)).ι).1
    rw [Category.assoc, zeroFunctorSCoreMap_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι,
      ← Category.assoc, zeroFunctorSCoreMap_ι]
    exact (exactSPostcomp_reindex F θ.unop.toOrderHom).symm

/-- 零圏への指定射では、相対商射影から作った同じ元の零角比較と厳密一致する。 -/
theorem zeroFunctorFullSMap_eq_zeroTarget {A Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A Z)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) :
    zeroFunctorFullSMap F hF = zeroTargetFullSMap F hZ := by
  apply NatTrans.ext
  funext n
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len Z.obj)).ι).1
  change zeroFunctorSCoreMap F hF n.unop.len ≫ _ =
    ((relativeSZeroTargetTopIso F hZ n.unop.len).inv ≫ relativeSQuotientMap F n.unop.len) ≫ _
  rw [zeroFunctorSCoreMap_ι, Category.assoc, relativeSQuotientMap_ι,
    ← relativeSZeroTargetTopIso_hom F hZ n.unop.len, Iso.inv_hom_id_assoc]
  rfl

/-- 元の core 制限では、任意の相対条件を経由しても指定完全関手の core S• 作用に等しい。 -/
theorem zeroFunctorFullSMap_core {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : A.obj ⟶ B.obj) (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C) (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    relativeSimplicialSConstructionCoreInclusion q ≫
        relativeSimplicialSConstructionInclusion q ≫ zeroFunctorFullSMap F hF = coreSExactMap F := by
  apply NatTrans.ext
  funext n
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len C.obj)).ι).1
  change (_ ≫ _ ≫ zeroFunctorSCoreMap F hF n.unop.len) ≫ _ = _
  rw [Category.assoc, Category.assoc, zeroFunctorSCoreMap_ι, ← Category.assoc]
  change (relativeDiagramCoreInclusion q (sComponentEvaluation A.obj n.unop.len) ≫
    (relativeDiagram q (sComponentEvaluation A.obj n.unop.len)).ι) ≫ (sExactMap n.unop.len F).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sExactMap n.unop.len F).hom ≫ _
  rw [relativeDiagramCoreInclusion_ι]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι ((sExactMap n.unop.len F).hom)).symm

end SerrePositivity.KST.Fibration
