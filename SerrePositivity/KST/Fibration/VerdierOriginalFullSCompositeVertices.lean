module
public import SerrePositivity.KST.Fibration.VerdierOriginalFullSHomFamily
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSKanComposite

/-!
概要：指定両端の全 S• path 比較の合成端を、元の実零値完全射の作用へ戻す。
方針：同じ安定 Hom の合成点と零値持ち上げの評価を厳密に回収する。
規約：元の二実合成完全射と全 S• 作用を保持する。
使われ方：K-6 c4 の動く上側第二短辺の両端を指定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration

private theorem fullSComposite_stable_vertex_transport {A B A' B' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (hA : A = A') (hB : B = B') (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    (eqToHom (congrArg₂ (fun (X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) =>
      SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) X Y) hA hB)).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B F) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A' B'
        (exactMapTransport hA hB F) := by
  cases hA
  cases hB
  rfl

/-- 概要：同じ元の安定全 path 族の合成点は、指定両端の元の実合成完全射。
方針：元の安定 Hom の頂点回収を同じ対象等号へ輸送する。
規約：元の実合成射を選び直さない。
使われ方：同じ全 S• 比較の合成端評価。 -/
theorem verdierOriginalStableHomFamily_full (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    (verdierOriginalStableHomFamily d j).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentTriangleFullPath) =
      SimplicialCategory.homEquiv' (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)
        (verdierNullCompositeOriginalMap d j) := by
  let h := congrArg₂ (fun (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) =>
    SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B)
      (verdierNullDiagonal_source d) (verdierNullDiagonal_target d)
  change (eqToHom h).app (Opposite.op ⦋0⦌) (verdierNullCompositeVertex d j) = _
  rw [← stableHom_homEquiv'_ExactMap (verdierNullCompositeVertex d j)]
  exact fullSComposite_stable_vertex_transport (verdierNullDiagonal_source d)
    (verdierNullDiagonal_target d) (verdierNullCompositeMap d j)

/-- 概要：元の指定合成完全射の同じ実全 S• Kan 作用。
方針：同じ零値完全射の全 S• 作用を実現して Kan 化する。
規約：元の実合成と零値証拠を保持する。
使われ方：動く上側第二短辺の元の指定両端。 -/
def verdierOriginalFullSCompositeMap (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    fullSRealizationKanObject d.left ⟶ stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map
    (zeroFunctorFullSMap (verdierNullCompositeOriginalMap d j)
      (isZeroVertex_functorVertex_of_pointwise _ (verdierNullCompositeOriginalMap_zero d j))))

/-- 概要：同じ全 S• 全 path 族の合成端は、元の指定零値完全射の実作用。
方針：同じ零値持ち上げの合成点を回収し、既存の実関手評価へ代入する。
規約：元の全 S• 作用そのものを保持する。
使われ方：K-6 c4 の上側第二短辺の始端・終端を照合する。 -/
theorem verdierOriginalFullSHomFamily_full (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    (verdierOriginalFullSHomFamily d j).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentTriangleFullPath) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject d.left).obj ⟶
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj from
          verdierOriginalFullSCompositeMap d j) := by
  have he : (zeroStableHomFamilyLift (verdierOriginalStableHomFamily d j)
      (verdierOriginalStableHomFamily_zero d j)).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleFullPath) =
      fullSubcategoryVertex _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (verdierNullCompositeOriginalMap d j).hom)
        (isZeroVertex_functorVertex_of_pointwise _ (verdierNullCompositeOriginalMap_zero d j)) := by
    apply Subtype.ext
    change (stableHomAmbient d.left d.right).app (Opposite.op ⦋0⦌)
      ((verdierOriginalStableHomFamily d j).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleFullPath)) = _
    rw [verdierOriginalStableHomFamily_full, stableHomAmbient_homEquiv']
    rfl
  change (zeroFunctorFullSKanFamily d.left d.right).app (Opposite.op ⦋0⦌)
    ((zeroStableHomFamilyLift (verdierOriginalStableHomFamily d j)
      (verdierOriginalStableHomFamily_zero d j)).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleFullPath)) = _
  rw [he]
  exact zeroFunctorFullSKanFamily_vertex _ _

/-- 概要：同じ動く全 S• 合成端族の始端は元の始端実合成完全射の作用。
方針：同じ比較円柱の始端を合成 path で評価する。
規約：元の指定完全射と実区間族を保持する。
使われ方：上側第二短辺の元の始端回収。 -/
theorem verdierOriginalFullSCompositePath_first (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    stdSimplex.δ (1 : Fin 2) ≫ verdierOriginalFullSCompositePath d j k =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject d.left).obj ⟶
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj from
          verdierOriginalFullSCompositeMap d j)) := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (verdierOriginalFullSHomComparison d j k).edge
  have hs : stdSimplex.δ (1 : Fin 2) ≫
      lift (SSet.const (Y := nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})
        (ComposableArrows.mk₀ coherentTriangleFullPath.{u}))
        (𝟙 (Δ[1] : SSet.{u})) =
      (SSet.const (X := (Δ[0] : SSet.{u})) (ComposableArrows.mk₀ coherentTriangleFullPath)) ≫
        SSet.ι₀ := by
    rw [stdSimplex.δ_one_eq_const]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    rfl
  change stdSimplex.δ (1 : Fin 2) ≫
    (lift (SSet.const (Y := nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})
        (ComposableArrows.mk₀ coherentTriangleFullPath.{u}))
      (𝟙 (Δ[1] : SSet.{u})) ≫ H.h) = _
  rw [← Category.assoc, hs, Category.assoc, H.h₀, SSet.const_comp,
    verdierOriginalFullSHomFamily_full, SSet.yonedaEquiv_symm_zero]

/-- 概要：同じ動く全 S• 合成端族の終端は元の終端実合成完全射の作用。
方針：同じ比較円柱の終端を合成 path で評価する。
規約：元の指定完全射と実区間族を保持する。
使われ方：上側第二短辺の元の商核側の終端回収。 -/
theorem verdierOriginalFullSCompositePath_last (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    stdSimplex.δ (0 : Fin 2) ≫ verdierOriginalFullSCompositePath d j k =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject d.left).obj ⟶
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj from
          verdierOriginalFullSCompositeMap d k)) := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (verdierOriginalFullSHomComparison d j k).edge
  have hs : stdSimplex.δ (0 : Fin 2) ≫
      lift (SSet.const (Y := nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})
        (ComposableArrows.mk₀ coherentTriangleFullPath.{u}))
        (𝟙 (Δ[1] : SSet.{u})) =
      (SSet.const (X := (Δ[0] : SSet.{u})) (ComposableArrows.mk₀ coherentTriangleFullPath)) ≫
        SSet.ι₁ := by
    rw [stdSimplex.δ_zero_eq_const]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    rfl
  change stdSimplex.δ (0 : Fin 2) ≫
    (lift (SSet.const (Y := nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})
        (ComposableArrows.mk₀ coherentTriangleFullPath.{u}))
      (𝟙 (Δ[1] : SSet.{u})) ≫ H.h) = _
  rw [← Category.assoc, hs, Category.assoc, H.h₁, SSet.const_comp,
    verdierOriginalFullSHomFamily_full, SSet.yonedaEquiv_symm_zero]

end SerrePositivity.KST.Fibration
