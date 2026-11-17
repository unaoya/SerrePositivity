module

public import SerrePositivity.EInfinity.BarrattEccles.WeightedCotensor
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.FrameLifting
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.Reindex

/-!
# 射影 cofibration に沿う右 frame の重み付き end の fibration

概要：BM 命題 4.1・Hovey §5.4 の右 frame で重みの射影 cofibration は fibration を誘導する。
方針：二重反対圏への前合成を使い、反対圏での実現の左類保存を適用する。
規約：単体集合の完全なモデル構造を仮定せず、実際の E 代数モデルを局所的に使う。
使われ方：cofibrant な一点重みによる一般 homotopy 極限の構成。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：重みの射影 cofibration は重み付き右 frame の fibration になる（Hovey §5.4）。
方針：同じ重みを二重反対化し、各値の右 frame の実現の cofibration 保存を使う。
規約：元の E 代数図式は任意で、cofibrancy の仮定を追加しない。
使われ方：重み付き錐の制限と一般極限の右持ち上げ性。 -/
lemma weightedCotensor_map_fibration (F : K ⥤ (operad A).Algebra)
    {W W' : K ⥤ SSet.{u}} (i : W ⟶ W') (hi : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries K).rlp.llp i) :
    let := modelCategory A
    Fibration ((weightedCotensor A K F).map i.op) := by
  let := modelCategory A
  have h := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.reindex_cofibration (opOpEquivalence K) i hi
  exact ⟨_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realization_map_cofibration Kᵒᵖ (rightFrameDiagram A K F)
    (fun k => rightFrame_cofibrant A (F.obj k.unop)) ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).map i) h⟩

end SerrePositivity.EInfinity.BarrattEccles
