module
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSNativeKanFamily

/-!
概要：全 S• の native Kan 族の各実点を、元の指定完全関手の同じ実射に同定する。
方針：単位からの固定関手式を零単体で評価し、元の全 Hom 頂点を厳密に回収する。
規約：パラメータの実頂点・元の完全射と指定 Verdier 左辺を保持する。
使われ方：coherent 中間対象輸送の短辺と、指定長 Hom の合成端の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration

/-- 元の零値完全関手の同じ全 S• 実射を、元の native Kan 標的に保持する。 -/
def zeroFunctorFullSNativeKanMap {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    fullSRealizationKanObject A ⟶ (stableMultiKanEnrichedFunctor 0).obj C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map (zeroFunctorFullSMap F hF)) ≫
    (coreSingleKanIso C).hom

/-- 全 native 族の指定実点は、同じ完全関手の全 S• 実射を表す。 -/
theorem zeroFunctorFullSNativeKanFamily_vertex {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    (zeroFunctorFullSNativeKanFamily A C).app (Opposite.op ⦋0⦌)
        (fullSubcategoryVertex _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom) hF) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject A).obj ⟶
        ((stableMultiKanEnrichedFunctor 0).obj C).obj from zeroFunctorFullSNativeKanMap F hF) := by
  have h := congrArg (SSet.unitHomEquiv _) (zeroFunctorFullSNativeKanFamily_fixed F hF)
  exact h

/-- 元の任意の Kan Hom 頂点の零値条件を、同じ元の完全射の条件として回収する。 -/
theorem stableHomZeroVertex_functorVertex {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (v : (A ⟶[SSet.{u}] C) _⦋0⦌) (hv : StableHomZeroVertex A C v) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (stableHomExactMap v).hom) :=
  stableHomAmbient_vertex v ▸ hv

/-- 元の全族の任意の実頂点でも、同じ元の完全射による全 S• 実射を回収する。 -/
theorem zeroStableHomFamilyLift_fullSNativeKan_vertex {P : SSet.{u}} {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (H : P ⟶ (A ⟶[SSet.{u}] C))
    (hH : ∀ v, StableHomZeroVertex A C (H.app (Opposite.op ⦋0⦌) v)) (v : P _⦋0⦌) :
    (zeroStableHomFamilyLift H hH ≫ zeroFunctorFullSNativeKanFamily A C).app
        (Opposite.op ⦋0⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject A).obj ⟶
        ((stableMultiKanEnrichedFunctor 0).obj C).obj from
          zeroFunctorFullSNativeKanMap (stableHomExactMap (H.app (Opposite.op ⦋0⦌) v))
            (stableHomZeroVertex_functorVertex _ (hH v))) := by
  have he : (zeroStableHomFamilyLift H hH).app (Opposite.op ⦋0⦌) v =
      fullSubcategoryVertex _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (stableHomExactMap (H.app (Opposite.op ⦋0⦌) v)).hom)
        (stableHomZeroVertex_functorVertex _ (hH v)) := by
    apply Subtype.ext
    exact stableHomAmbient_vertex _
  change (zeroFunctorFullSNativeKanFamily A C).app _
    ((zeroStableHomFamilyLift H hH).app _ v) = _
  rw [he, zeroFunctorFullSNativeKanFamily_vertex]

/-- 指定 Verdier 左辺の実射は、同じ元の native 零角比較そのもの。 -/
theorem zeroFunctorFullSNativeKanMap_verdierLeft (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    zeroFunctorFullSNativeKanMap (verdierLeftExactMap d) (verdierLeftExactMap_zero d) =
      verdierFullSZeroCornerNativeKanMap d := rfl

end SerrePositivity.KST.Fibration
