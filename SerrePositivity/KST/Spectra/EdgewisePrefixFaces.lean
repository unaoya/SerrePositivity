module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PrefixOverWeight
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseEndpoints

/-!
概要：共通 edgewise 切断の初区間の始点は、元の図式の射による始点係数の像である。
方針：初区間の自然変換の 0→1 の自然性を、標準区間の始点面として読む。
規約：元の初区間の重みと係数を保持。使われ方：cospan の三単体の内辺を定値へ同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.EdgewiseCoordinates
variable {I : Type u} [SmallCategory I] {H : I ⥤ SSet.{u}}

/-- 元の初区間の始点面は、元の始点の切断と図式の射の合成そのもの。 -/
lemma prefix_source
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⟶ H ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor) (σ : ComposableArrows I 1) :
    stdSimplex.δ (1 : Fin 2) ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ).app (1 : Fin 2) ≫ η.app (σ.obj (1 : Fin 2))) =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ).app (0 : Fin 2) ≫ η.app (σ.obj (0 : Fin 2))) ≫
        (H ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor).map (σ.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))) := by
  let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ ≫ Functor.whiskerLeft σ η
  have hh := τ.naturality (homOfLE (by decide : (0 : Fin 2) ≤ 1))
  have hp : stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion 0 1 (by decide)) =
      (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
    apply SSet.yonedaEquiv.injective
    decide
  change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion 0 1 (by decide)) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ).app (1 : Fin 2) ≫ η.app (σ.obj (1 : Fin 2))) = _ at hh
  rw [hp] at hh
  exact hh

end SerrePositivity.KST.Spectra.EdgewiseCoordinates
