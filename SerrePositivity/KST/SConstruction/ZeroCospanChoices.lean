module
public import SerrePositivity.KST.SConstruction.ZeroCospanData
public import SerrePositivity.KST.SConstruction.LimitBaseTransport
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition

/-! # 固定した第一辺の零脚の比較
概要：同じ第一辺を持ち、第二辺が零対象から出る二つの cospan は coherent に同型である。
方針：零脚のデータの trivial Kan fibration の同じ fiber 内で比較する。
規約：零頂点と零射を厳密に保持してデータへ含める。
使われ方：BGT Lemma 7.3、指定した零脚の cospan の極限の存在。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：第一辺の等しい零脚つき cospan の族は coherent に同型。
方針：零脚のデータに持ち上げ、trivial Kan fibration の同じ持ち上げ同士を比較する。
規約：C は零対象を持つだけでよい。使われ方：パラメーター付き零脚の選択の変更。 -/
def zeroCospanFamiliesIso {A C : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C]
    (p q : A ⟶ (ihom (horn 2 2 : SSet.{u})).obj C)
    (hp : ∀ v : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow
      (((pre horn₂₂.ι₁₂).app C).app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) v)))
    (hq : ∀ v : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow
      (((pre horn₂₂.ι₁₂).app C).app (Opposite.op ⦋0⦌) (q.app (Opposite.op ⦋0⦌) v)))
    (h : p ≫ (pre horn₂₂.ι₀₂).app C = q ≫ (pre horn₂₂.ι₀₂).app C) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso p q := by
  have he : zeroCospanDataLift p hp ≫ zeroCospanDataProjection C =
      zeroCospanDataLift q hq ≫ zeroCospanDataProjection C := by
    rw [zeroCospanDataLift_projection, zeroCospanDataLift_projection, h]
  have e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration (zeroCospanDataProjection C)
    (zeroCospanDataLift p hp) (zeroCospanDataLift q hq) he).postcomp (zeroCospanDataDiagram C)
  simpa only [zeroCospanDataLift_diagram] using e

/-- 概要：同じ第一辺を持つ二つの零脚つき cospan の図式は関手として同型。
方針：一点パラメーターの族として比較し、その点で評価する。
規約：同型は全 cospan の coherent な同型。使われ方：極限の存在を任意の零脚に移す。 -/
def zeroCospanDiagramsIso {C : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C]
    (p q : (horn 2 2 : SSet.{u}) ⟶ C)
    (hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₂.ι₁₂ ≫ p)))
    (hq : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₂.ι₁₂ ≫ q)))
    (h : horn₂₂.ι₀₂ ≫ p = horn₂₂.ι₀₂ ≫ q) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso p q := by
  let P : (Δ[0] : SSet.{u}) ⟶ (ihom (horn 2 2 : SSet.{u})).obj C := SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)
  let Q : (Δ[0] : SSet.{u}) ⟶ (ihom (horn 2 2 : SSet.{u})).obj C := SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q)
  have hP (v : (Δ[0] : SSet.{u}) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow
      (((pre horn₂₂.ι₁₂).app C).app (Opposite.op ⦋0⦌) (P.app (Opposite.op ⦋0⦌) v)) := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow (((pre horn₂₂.ι₁₂).app C).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) 0))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact hp
  have hQ (v : (Δ[0] : SSet.{u}) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow
      (((pre horn₂₂.ι₁₂).app C).app (Opposite.op ⦋0⦌) (Q.app (Opposite.op ⦋0⦌) v)) := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow (((pre horn₂₂.ι₁₂).app C).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q) 0))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact hq
  have hPQ : P ≫ (pre horn₂₂.ι₀₂).app C = Q ≫ (pre horn₂₂.ι₀₂).app C := by
    rw [SSet.const_comp, SSet.const_comp]
    change SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₂.ι₀₂ ≫ p)) =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₂.ι₀₂ ≫ q))
    rw [h]
  let e := zeroCospanFamiliesIso P Q hP hQ hPQ
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) 0)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q) 0) at he
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using he

/-- 概要：安定な標的では零対象から出る脚を持つ cospan が極限を持つ。
方針：同じ第一辺の選んだ fiber の cospan と同型で比較する。
規約：指定された零脚を保持する。使われ方：関手圏の点ごとの fiber の存在。 -/
lemma hasLimit_zeroCospan {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (p : (horn 2 2 : SSet.{u}) ⟶ C)
    (hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₂.ι₁₂ ≫ p))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p := by
  let f := horn₂₂.ι₀₂ ≫ p
  let t := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenFiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv f))
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ t.square = f := by
    rw [t.right_edge]
    exact SSet.yonedaEquiv.symm_apply_apply f
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square
  have hq : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₂.ι₁₂ ≫ q)) := by
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₂.ι₁₂ ≫ q)))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((horn₂₂.ι₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ t.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge]
    exact t.zero_corner
  have he : horn₂₂.ι₀₂ ≫ p = horn₂₂.ι₀₂ ≫ q := by
    change f = horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ t.square
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge, ht]
  exact HasLimit.of_functorIso ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square, t.isPullback⟩
    (zeroCospanDiagramsIso p q hp hq he)

end SerrePositivity.KST.SConstruction
