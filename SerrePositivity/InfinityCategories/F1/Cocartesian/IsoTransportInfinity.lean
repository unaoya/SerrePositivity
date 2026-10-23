module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportDiagramComparison
public import SerrePositivity.InfinityCategories.F1.Categories.CoreEnrichedFunctor

/-!
概要：指定同型の始域の元の全 Hom の core から、比較の源の実際の ∞ 圏を作る。
方針：同じ豊穣圏の core の移送を行い、元の Hom の Kan 性を使う。
規約：別の写像空間を選ばず、全局所 Hom の同じ core を保持する。
使われ方：結合共役の全局所比較を coherent な族へ実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 指定同型と、始域の元の全相対 Hom の core の豊穣圏。 -/
def CocartesianIsoTransportCategory (A : Type u) [Category.{u} A] : Type (u + 1) :=
  TransportEnrichment quasicategoryCoreFunctor.{u}
    (IsoTransportObject (CocartesianFibrationObject (nerve A)))

instance cocartesianIsoTransportCategory_category (A : Type u) [Category.{u} A] :
    Category.{u} (CocartesianIsoTransportCategory A) :=
  inferInstanceAs (Category.{u}
    (TransportEnrichment quasicategoryCoreFunctor.{u}
      (IsoTransportObject (CocartesianFibrationObject (nerve A)))))

instance cocartesianIsoTransportCategory_simplicialCategory (A : Type u) [Category.{u} A] :
    SimplicialCategory (CocartesianIsoTransportCategory A) :=
  TransportEnrichment.enrichedOrdinaryCategory
    (IsoTransportObject (CocartesianFibrationObject (nerve A))) quasicategoryCoreFunctor.{u}
    quasicategoryCoreUnitHomEquiv quasicategoryCoreUnitHomEquiv_eq

/-- 同じ元の全相対 Hom の core は Kan 複体。 -/
instance cocartesianIsoTransportCategory_sHom_kanComplex
    {A : Type u} [Category.{u} A] (X Y : CocartesianIsoTransportCategory A) :
    KanComplex (SimplicialCategory.sHom X Y) := by
  change KanComplex (quasicategoryCore
    (cocartesianRelativeFunctorSpace X.source.val.hom Y.source.val.hom) : SSet.{u})
  infer_instance

/-- 同じ全局所 Hom の core を保持する、指定同型の実際の ∞ 圏。 -/
def CocartesianIsoTransportInfinity (A : Type u) [Category.{u} A] : SSet.{u + 1} :=
  SimplicialNerve (CocartesianIsoTransportCategory A)

instance cocartesianIsoTransportInfinity_quasicategory (A : Type u) [Category.{u} A] :
    Quasicategory (CocartesianIsoTransportInfinity A) :=
  Coherent.simplicialNerve_quasicategory (CocartesianIsoTransportCategory A)

/-- 同じ比較の源の豊穣 Hom は、元の二重引き戻し間の全 Hom の core そのもの。 -/
lemma cocartesianIsoTransportCategory_native_sHom
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    SimplicialCategory.sHom
      (show CocartesianIsoTransportCategory A from cocartesianBaseChangeIsoTransportObject l k p)
      (show CocartesianIsoTransportCategory A from cocartesianBaseChangeIsoTransportObject l k q) =
    SimplicialCategory.sHom
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p))
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) := rfl

end SerrePositivity.InfinityCategories
