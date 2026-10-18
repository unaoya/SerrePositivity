module

public import SerrePositivity.KST.Spectra.PointedWeightedEndBifunctor
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
概要：単体的な重みから作る余単体 cochain 図式と係数への関手性。
方針：重みに関する反変 end と係数に関する共変 end の可換性を使う。
規約：単体的な恒等式は厳密な関手の法則として実現する。
使われ方：Goerss–Jardine VIII §§1–2、HA §1.4.2。群作用の cochain の共通部分。
-/

@[expose] public section

universe u

open CategoryTheory SSet Opposite

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：単体的な重みと固定した点つき係数から余単体 cochain 図式を作る。
方針：重みの反対関手と end の重みに関する反変関手を合成する。
規約：全ての余単体恒等式は通常の関手の法則として成立する。
使われ方：Goerss–Jardine VIII §2。群作用の cochain の構造射。 -/
def weightedCochains {I : Type u} [SmallCategory I]
    (W : SimplicialObject (I ⥤ SSet.{u})) (D : I ⥤ PointedSimplicialSet.{u}) :
    CosimplicialObject PointedSimplicialSet.{u} :=
  W.rightOp ⋙ PointedWeightedEnd.weightFunctor D

/-- 概要：点つき係数の自然変換が誘導する余単体 cochain の射。
方針：重みを固定して各次数で係数への後合成を行う。
規約：重みの前合成との可換性が余単体の自然性を与える。
使われ方：Goerss–Jardine VIII §2。群作用の射への cochain の自然性。 -/
def weightedCochainsMap {I : Type u} [SmallCategory I]
    (W : SimplicialObject (I ⥤ SSet.{u}))
    {D E : I ⥤ PointedSimplicialSet.{u}} (τ : D ⟶ E) :
    weightedCochains W D ⟶ weightedCochains W E where
  app n := PointedWeightedEnd.map (W.obj (op n)) τ
  naturality _m _n f :=
    (PointedWeightedEnd.map_preMap (W.map f.op) τ).symm

/-- 概要：固定した単体的重みの余単体 cochain は係数に関する関手。
方針：各次数の end の関手法則を余単体自然変換へ持ち上げる。
規約：Kan 性はこの関手の構成には不要。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。群作用の cochain の係数比較。 -/
def weightedCochainsFunctor {I : Type u} [SmallCategory I]
    (W : SimplicialObject (I ⥤ SSet.{u})) :
    (I ⥤ PointedSimplicialSet.{u}) ⥤ CosimplicialObject PointedSimplicialSet.{u} where
  obj := weightedCochains W
  map := weightedCochainsMap W
  map_id D := by
    apply NatTrans.ext
    funext n
    exact PointedWeightedEnd.map_id (W.obj (op n)) D
  map_comp τ υ := by
    apply NatTrans.ext
    funext n
    exact PointedWeightedEnd.map_comp (W.obj (op n)) τ υ

end

end SerrePositivity.KST.Spectra
