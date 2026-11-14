module
public import SerrePositivity.KST.Fibration.VerdierUpperFullSMap
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSCoreRestriction

/-!
概要：元の全 S• を零角とする、指定 Verdier 左辺の実可逆 Kan 比較。
方針：全 S_n の零対象による収縮を実現し、同じ指定零値関手の実射の可逆性を反映する。
規約：終対象間同型へ取り替えず、元の左辺・上辺との厳密な因子分解を保持する。
使われ方：元の二胞体を保つ coherent 中間対象輸送の実入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants

open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の全 S• 実現の同じ一点への実射は、零対象による各段の収縮から可逆。 -/
theorem fullSRealization_toPoint_localized_isIso (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from
      (simplicialDiagonalFunctor.obj (simplicialSConstruction A.obj)))) := by
  let F := simplicialSConstruction A.obj
  let c := simplicialSpaceToPoint F
  have hd : IsIso (AnodyneHomotopy.anodyneQ.map (simplicialDiagonalFunctor.map c)) := by
    apply BisimplicialModel.localized_diagonal_map
    intro n
    exact initialVertex_toPoint_localized_isIso
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex (sConstruction n.unop.len A.obj)).isZero.1
  have he : simplicialDiagonalFunctor.map c ≫ (constantSSetDiagonalIso (⊤_ SSet.{u})).hom =
      terminal.from (simplicialDiagonalFunctor.obj F) := terminal.hom_ext _ _
  change IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from (simplicialDiagonalFunctor.obj F)))
  rw [← he, Functor.map_comp]
  infer_instance

/-- 全 S• の元の実 Ex∞ Kan 頂点は、同じ一点射により終対象。 -/
theorem fullSRealizationKanObject_isTerminal (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (fullSRealizationKanObject A)) :=
  exInfinityVertex_isTerminal_of_localized_toPoint _
    (fullSRealization_toPoint_localized_isIso A)

/-- 指定した零圏への全 S• 実射そのものが局所化可逆。 -/
theorem zeroFunctorFullSMap_localized_isIso {A Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A Z)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (zeroFunctorFullSMap F hF))) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  let g := simplicialDiagonalFunctor.map (zeroFunctorFullSMap F hF)
  have hs := fullSRealization_toPoint_localized_isIso A
  have ht := coreSZeroTarget_toPoint_localized_isIso Z hZ
  have he : g ≫ terminal.from _ = terminal.from _ := terminal.hom_ext _ _
  have hc : IsIso (Q.map g ≫ Q.map (terminal.from _)) := by
    rw [← Functor.map_comp, he]
    exact hs
  exact (isIso_comp_right_iff _ _).mp hc

/-- 元の指定左辺を全 S• に作用させた同じ実 Kan 射。 -/
def verdierFullSZeroCornerKanMap (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    fullSRealizationKanObject d.left ⟶
      stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.square 0 1)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map
    (zeroFunctorFullSMap (verdierLeftExactMap d) (verdierLeftExactMap_zero d)))

/-- 同じ元の全 S• 零角比較の coherent 辺は可逆。 -/
theorem verdierFullSZeroCornerKanMap_isInvertible (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (verdierFullSZeroCornerKanMap d)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isQCatEquivalence_of_anodyneQ_isIso
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_localized_isIso_iff _).mpr
    (zeroFunctorFullSMap_localized_isIso _ _ d.zero_corner)

/-- 元の実左辺は、元の core 包含と同じ実可逆零角比較の厳密合成。 -/
theorem verdierFullSZeroCornerKanMap_left (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)) ≫
        verdierFullSZeroCornerKanMap d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map (coreSExactMap (verdierLeftExactMap d))) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _
  rw [← Functor.map_comp, coreSFullRealizationInclusion, ← Functor.map_comp]
  exact congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map f))
    (by simpa only [Category.assoc] using
      zeroFunctorFullSMap_core (𝟙 d.left.obj) (verdierLeftExactMap d) (verdierLeftExactMap_zero d))

/-- 零角比較と元の指定上辺の合成も、同じ上側合成の実全 S• 射に厳密一致する。 -/
theorem verdierFullSZeroCornerKanMap_top (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    verdierFullSZeroCornerKanMap d ≫
        (show stableCoreSingleKanObject
          (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.square 0 1)) ⟶
            stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right) from
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map (coreSExactMap (verdierTopExactMap d)))) =
      (show fullSRealizationKanObject d.left ⟶
        stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right) from
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map
            (zeroFunctorFullSMap (verdierNullCompositeOriginalMap d 0) (verdierUpperComposite_zero d)))) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _
  rw [← Functor.map_comp, ← Functor.map_comp, verdierUpperFullSMap_comp]

end SerrePositivity.KST.Fibration
