module
public import SerrePositivity.KST.Fibration.VerdierMovingUpperLastTriangle
public import SerrePositivity.KST.Fibration.VerdierFullSMovingSquarePrism

/-!
概要：動く上側の標準終端二胞体を、同じ実全 S• 商核の上側へ厳密に照合する。
方針：同じ実読出しの合成端を元の包含・商の厳密合成へ戻す。
規約：新しい商・局所化 API を作らず、元の二実射と標準二胞体を保持する。
使われ方：K-6 c4 の正規化四角柱の終端から c5 の同じ実商核への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration

/-- 概要：動く第二短辺の終端は元の包含・商の全 S• 零値作用そのもの。
方針：同じ実合成完全射の厳密回収を実現・Kan 化へ送る。
規約：零値証拠の取り方に依存しない。使われ方：同じ商核上辺の回収。 -/
theorem verdierOriginalFullSCompositeMap_last_kernel (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    verdierOriginalFullSCompositeMap d 1 =
      exInfinityKanMap (simplicialDiagonalFunctor.map (zeroFunctorFullSMap
        (show d.left ⟶ d.right from (show d.left ⟶ d.middle from d.inclusion) ≫
          (show d.middle ⟶ d.right from d.projection))
        (verdierSequenceComposite_zero d.isVerdier))) := by
  have hc : ∀ (F G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap d.left d.right) (h : F = G)
      (hf : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) (hg : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G.hom)),
      zeroFunctorFullSMap F hf = zeroFunctorFullSMap G hg := by
    intro F G h hf hg
    subst G
    rfl
  exact congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map f))
    (hc _ _ (verdierNullCompositeOriginalMap_lower d) _ _)

/-- 概要：同じ標準上側終端は元の全 S• 商核の上側全二胞体。
方針：実商核の coherent 標準合成と同じ二実射へ双方を戻す。
規約：二辺だけの比較に弱めず、二胞体全体を厳密回収する。
使われ方：正規化四角柱の有限終端の全四角形同定。 -/
theorem verdierMovingUpperLastTriangle_kernel (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    SSet.yonedaEquiv.symm (verdierMovingUpperLastTriangle d).simplex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ quotientSKernelFullInfinitySquare d.isVerdier := by
  rw [quotientSKernelFullInfinitySquare, exInfinityCommSqInfinitySquare,
    kanCommSqInfinitySquare_upper_compStruct, verdierMovingUpperLastTriangle,
    verdierOriginalFullSCompositeMap_last_kernel]
  rfl

end SerrePositivity.KST.Fibration
