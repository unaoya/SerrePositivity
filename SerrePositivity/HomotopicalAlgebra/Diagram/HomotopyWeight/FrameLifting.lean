module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.Generators
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightRealization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryTensor

/-!
# 射影重みに対する frame の重み付き実現の持ち上げ

概要：Hovey §5.4 の重み付き実現が射影境界の左類を cofibration へ移すことを証明する。
方針：実際の随伴と各成分の境界持ち上げを使う。
規約：単体集合の完全なモデル構造は仮定しない。
使われ方：E 代数の重み付き右 frame の end の fibration 判定。
-/

@[expose] public section

noncomputable section

universe u v

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.DiagramModel

variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u, u} C] [ModelCategory C]
  (B : K ⥤ SimplexCategory ⥤ C)
  (hB : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B.obj k)))

include hB

/-- 概要：射影境界の左類の重みの射を実現すると cofibration になる（Hovey §5.4）。
方針：trivial fibration の Hom が各成分で境界の右類になることを使う。
規約：射影の左類そのものを入力し、頂点ごとの単射へ弱めない。
使われ方：一般 homotopy 極限の cofibrant 重みの制限。 -/
lemma realization_map_cofibration {W W' : Kᵒᵖ ⥤ SSet.{u}} (i : W ⟶ W')
    (hi : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries Kᵒᵖ).rlp.llp i) :
    cofibrations C ((FrameWeightRealization.functor K B).map i) := by
  rw [← trivialFibrations_llp]
  intro X Y p hp
  have : Fibration p := ⟨hp.1⟩
  have : WeakEquivalence p := ⟨hp.2⟩
  apply ((FrameWeightRealization.adjunction K B).hasLiftingProperty_iff i p).mpr
  apply hi
  apply (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries_rlp Kᵒᵖ).ge
  intro k X Y f hf
  obtain ⟨n⟩ := hf
  exact boundary_lifting_of_reedyCofibrant (B.obj k.unop) n (hB k.unop) p

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
