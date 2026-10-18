module

public import SerrePositivity.KST.Spectra.WeightedCochains

/-!
概要：単体的な重みの同型による点つき cochain 図式の同型。
方針：重みの反対関手の自然同型を作り、反変な end 関手を後合成する。
規約：自然同型全体を使い、全ての顔・退化への自然性を保持する。
使われ方：Goerss–Jardine VIII §2。EG の斉次座標と非斉次座標の cochain の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.WeightedCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I]

/-- 概要：単体的な重みの自然同型を反対の重み図式の自然同型にする。
方針：順逆の成分を反対射へ送り、向きの反転を補う。
規約：始域と終域の重みの順序を保つため逆射から順射を作る。
使われ方：Goerss–Jardine VIII §2。cochain の重みの変更の入力。 -/
def rightWeightIso {W V : SimplicialObject (I ⥤ SSet.{u})} (e : W ≅ V) :
    W.rightOp ≅ V.rightOp where
  hom := e.inv.rightOp
  inv := e.hom.rightOp
  hom_inv_id := by
    rw [← NatTrans.rightOp_comp, e.hom_inv_id, NatTrans.rightOp_id]
  inv_hom_id := by
    rw [← NatTrans.rightOp_comp, e.inv_hom_id, NatTrans.rightOp_id]

/-- 概要：重みの自然同型は点つき cochain の実際の余単体図式の同型を誘導する。
方針：反対の重みの同型に係数を固定した end 関手を後合成する。
規約：係数の Kan 性は不要。
使われ方：Goerss–Jardine VIII §2。群 cochain の非斉次座標の比較。 -/
def weightIso {W V : SimplicialObject (I ⥤ SSet.{u})} (e : W ≅ V)
    (D : I ⥤ PointedSimplicialSet.{u}) : weightedCochains W D ≅ weightedCochains V D :=
  Functor.isoWhiskerRight (rightWeightIso e) (PointedWeightedEnd.weightFunctor D)

end

end SerrePositivity.KST.Spectra.WeightedCochains
