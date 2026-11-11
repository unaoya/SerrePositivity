module
public import SerrePositivity.KST.SConstruction.CutSupportVanishing
public import SerrePositivity.KST.SConstruction.CofiberFamilyVanishingIsos

/-! # 支持部分圏の切断による正規化
概要：左支持の min 切断と元の包含、右支持の max 切断と元の包含を関手同型で比較する。
方針：切断 cofiber 族の反対側の項の消滅を関手圏の零 cofiber 判定へ渡す。
規約：点ごとの同型の寄せ集めにしない。使われ方：短い区間の S 構成との実際の同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 任意の族への切断比較の前合成は元の各角の評価を保持する。 -/
lemma cutComparison_pre_evaluation {K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (n : ℕ) (k : Fin (n + 1)) (f : K ⟶ sConstruction n C) (x y : Fin 2) :
    (f ≫ cutCofiberComparison n k C) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y) =
      f ≫ sMap C (cutCornerOrder k x y) := by
  exact (Category.assoc _ _ _).trans
    (congrArg (fun g => f ≫ g) (cutCofiberComparison_evaluation n k C x y))

/-- 切断比較の任意の前合成の中央評価は元の族そのもの。 -/
lemma cutComparison_pre_middle {K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (n : ℕ) (k : Fin (n + 1)) (f : K ⟶ sConstruction n C) :
    (f ≫ cutCofiberComparison n k C) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = f := by
  have h := cutComparison_pre_evaluation n k f 1 0
  rw [cutCornerOrder_one_zero, sMap_id, Category.comp_id] at h
  exact h

/-- 左支持の min 切断は元の包含と coherent な関手同型で比較される。 -/
def cutLeftSupport_normalizationIso (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((closedStableInclusion (cutLeftSupport n k X)).val ≫ sMap X.carrier (cutCornerOrder k 0 0))
      (closedStableInclusion (cutLeftSupport n k X)).val := by
  let i := (closedStableInclusion (cutLeftSupport n k X)).val
  let H := i ≫ cutCofiberComparison n k X.carrier
  have e := cofiberFamilyBottomIso H (by
    intro v
    have he := congrArg (fun f => f.app (Opposite.op ⦋0⦌) v)
      (cutComparison_pre_evaluation n k i 1 1)
    exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex he).mpr
      (cutLeftSupport_rightCut_isZero n k X v.val (closedSubcategory_vertex _ v)))
  have hs := cutComparison_pre_evaluation n k i 0 0
  have hm := cutComparison_pre_middle n k i
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((i ≫ cutCofiberComparison n k X.carrier) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _)
    ((i ≫ cutCofiberComparison n k X.carrier) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _) at e
  rw [hs, hm] at e
  exact e

/-- 右支持の元の包含は max 切断と coherent な関手同型で比較される。 -/
def cutRightSupport_normalizationIso (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (closedStableInclusion (cutRightSupport n k X)).val
      ((closedStableInclusion (cutRightSupport n k X)).val ≫
        sMap X.carrier (cutCornerOrder k 1 1)) := by
  let i := (closedStableInclusion (cutRightSupport n k X)).val
  let H := i ≫ cutCofiberComparison n k X.carrier
  have e := cofiberFamilyRightIso H (by
    intro v
    have he := congrArg (fun f => f.app (Opposite.op ⦋0⦌) v)
      (cutComparison_pre_evaluation n k i 0 0)
    exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex he).mpr
      (cutRightSupport_leftCut_isZero n k X v.val (closedSubcategory_vertex _ v)))
  have hm := cutComparison_pre_middle n k i
  have hq := cutComparison_pre_evaluation n k i 1 1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((i ≫ cutCofiberComparison n k X.carrier) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _)
    ((i ≫ cutCofiberComparison n k X.carrier) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _) at e
  rw [hm, hq] at e
  exact e

end SerrePositivity.KST.SConstruction
