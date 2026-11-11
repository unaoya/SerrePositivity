module

public import SerrePositivity.KST.Spectra.EdgewisePrefixFaces
public import SerrePositivity.KST.Spectra.EdgewiseTetrahedronCoordinates
public import SerrePositivity.KST.Spectra.CospanPrefixCoordinates
public import SerrePositivity.KST.Spectra.LoopIntervalEndFamilies

/-!
概要：loop 係数の元の edgewise 切断の二つの三単体は、定値内辺と共通の外辺を持つ。
方針：初区間の自然性を一点係数の定値射へ移し、共通の中央 over 頂点を使う。
規約：元の BK 切断全体から証明し、内辺や外辺の条件を仮定にしない。
使われ方：円評価錐の反転比較の符号と、apex の経路の厳密な照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.LoopEdgewiseSection

/-- 元の cospan の k 番目の射の列。 -/
abbrev arrow (k : WalkingPair) : ComposableArrows (AsSmall.{u} WalkingCospan) 1 :=
  ComposableArrows.mk₁ (AsSmall.up.map (WidePullbackShape.Hom.term k))

/-- 元の BK 切断の k 番目の初区間を評価した、中央係数の同じ解像一単体の区間。 -/
def parameter (Y : PointedSimplicialSet.{u})
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan) ⟶
      loopCoefficient Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor) (k : WalkingPair) :
    (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision Y.right :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight (arrow k)).app (1 : Fin 2) ≫ η.app (AsSmall.up.obj .one)

/-- 元の解像一単体の始点は、基点での定値辺そのもの。 -/
lemma initialFace (Y : PointedSimplicialSet.{u})
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan) ⟶
      loopCoefficient Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor) (k : WalkingPair) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision Y.right).δ 1 (SSet.yonedaEquiv (parameter Y η k)) =
      SSet.const (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋0⦌) Y.basepoint := by
  cases k
  all_goals
    rw [← stdSimplex.yonedaEquiv_δ_comp, parameter]
    erw [EdgewiseCoordinates.prefix_source, SSet.yonedaEquiv_comp]
    change _ ≫ SSet.const Y.basepoint = _
    exact SSet.comp_const _ _

/-- 二つの元の解像一単体の終点は、元の中央 over 頂点での同じ切断値。 -/
lemma finalFaces_common (Y : PointedSimplicialSet.{u})
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan) ⟶
      loopCoefficient Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision Y.right).δ 0 (SSet.yonedaEquiv (parameter Y η .left)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision Y.right).δ 0 (SSet.yonedaEquiv (parameter Y η .right)) := by
  have h := congrArg (fun f : (Δ[0] : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)).obj (AsSmall.up.obj .one) ↦
        f ≫ η.app (AsSmall.up.obj .one)) CospanShape.prefix_target_common
  simp only [Category.assoc] at h
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.yonedaEquiv_δ_comp]
  exact congrArg SSet.yonedaEquiv h

/-- 元の二つの三単体の各内辺 (1,2) は、元の標的の基点で定値。 -/
lemma innerCurve_constant (Y : PointedSimplicialSet.{u})
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan) ⟶
      loopCoefficient Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor) (k : WalkingPair) :
    SSet.yonedaEquiv.symm (stdSimplex.edge 3 1 2 (by decide)) ≫
      EdgewiseCoordinates.tetrahedronMap (SSet.yonedaEquiv (parameter Y η k)) =
        SSet.const Y.basepoint := by
  rw [← EdgewiseCoordinates.oneFace]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 0).inv ≫ _ = _
  rw [initialFace, SSet.comp_const]

/-- 元の二つの三単体の各外辺 (0,3) は、同じ元の apex の経路に厳密一致する。 -/
lemma outerCurves_common (Y : PointedSimplicialSet.{u})
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan) ⟶
      loopCoefficient Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor) :
    SSet.yonedaEquiv.symm (stdSimplex.edge 3 0 3 (by decide)) ≫
        EdgewiseCoordinates.tetrahedronMap (SSet.yonedaEquiv (parameter Y η .left)) =
      SSet.yonedaEquiv.symm (stdSimplex.edge 3 0 3 (by decide)) ≫
        EdgewiseCoordinates.tetrahedronMap (SSet.yonedaEquiv (parameter Y η .right)) := by
  rw [← EdgewiseCoordinates.zeroFace, ← EdgewiseCoordinates.zeroFace, finalFaces_common]

end SerrePositivity.KST.Spectra.LoopEdgewiseSection
