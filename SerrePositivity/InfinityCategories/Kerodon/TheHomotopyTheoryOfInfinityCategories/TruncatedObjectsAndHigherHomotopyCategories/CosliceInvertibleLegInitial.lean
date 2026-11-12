module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLeg
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IdentityCocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
# 可逆な脚を持つ一点の余錐の始対象性

## 概要
一点の図式からの余錐で、その指定された脚が可逆なら、同じ余錐は coslice の始対象。

## 方針
恒等余錐からの辺の脚の三角形を読み、左ファイブレーションで可逆性を反映する。

## 規約
余錐を別の頂点のものへ取り替えない。

## 使われ方
Kerodon 4.7（Tag 05EA）、4.4.2（Tag 019F）。指定した bar の閉射を持つ余錐の余極限判定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 可逆な指定脚を持つ一点の余錐は、その coslice で始対象となる。 -/
theorem coslice_isInitialVertex_of_invertible_leg {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) (c : JoinCocone (SSet.yonedaEquiv.symm x))
    (h : IsInvertibleEdge (c.leg (𝟙 Δ[0]))) :
    IsInitialVertex (X := sliceUnder (SSet.yonedaEquiv.symm x)) c := by
  let c₀ : JoinCocone (SSet.yonedaEquiv.symm x) := cosliceIdentityCone x
  have hc₀ : IsInitialVertex (X := sliceUnder (SSet.yonedaEquiv.symm x)) c₀ := cosliceIdentityCone_isInitialVertex x
  obtain ⟨e⟩ := hc₀.nonempty_edge c
  have h₀ : (c₀.leg (𝟙 Δ[0])).edge = (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x).edge := by
    change SSet.yonedaEquiv (_ ≫ SSet.const x) = _
    rw [SSet.comp_const]
    change X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op x = X.map (SimplexCategory.σ 0).op x
    exact congrArg (fun f : ⦋1⦌ ⟶ ⦋0⦌ => X.map f.op x) (Subsingleton.elim _ _)
  have hi₀ : IsInvertibleEdge (c₀.leg (𝟙 Δ[0])) :=
    (isInvertibleEdge_congr h₀).mpr (by
      change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x))
      rw [SSet.Truncated.HomotopyCategory.homMk_id]
      infer_instance)
  let q := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  have ht := JoinCocone.leg_comp_projection e (𝟙 Δ[0])
  haveI : IsIso (SSet.Truncated.HomotopyCategory.homMk (c₀.leg (𝟙 Δ[0]))) := hi₀
  haveI : IsIso (SSet.Truncated.HomotopyCategory.homMk (c₀.leg (𝟙 Δ[0])) ≫
      SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map q))) := by
    rw [ht]
    exact h
  have hb : IsInvertibleEdge (e.map ((truncation 2).map q)) :=
    IsIso.of_isIso_comp_left (SSet.Truncated.HomotopyCategory.homMk (c₀.leg (𝟙 Δ[0]))) _
  haveI : IsIso (SSet.Truncated.HomotopyCategory.homMk e) :=
    leftFibration_reflects_invertibleEdge q e hb
  exact hc₀.of_vertexIso (asIso (SSet.Truncated.HomotopyCategory.homMk e))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
