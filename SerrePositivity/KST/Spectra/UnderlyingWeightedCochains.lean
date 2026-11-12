module

public import SerrePositivity.KST.Spectra.PointedWeightedEndUnderlyingWeight
public import SerrePositivity.KST.Spectra.WeightedCochains

/-!
概要：単体的重みの通常の cochain と点つき cochain の忘却の比較。
方針：通常の end の反変重み関手を作り、点つき end の比較を余単体図式へ束ねる。
規約：基礎単体集合の実際の余単体図式の同型。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。通常の Tot の密度比較への入力。
-/

@[expose] public section

universe u

open CategoryTheory SSet Opposite


namespace SerrePositivity.KST.Spectra.UnderlyingWeightedCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I]

/-- 概要：通常の end を重みに関する反変関手として束ねる。
方針：重みの前合成の恒等・合成法則を使う。
規約：係数図式は固定する。
使われ方：Goerss–Jardine VIII §1。通常の cochain の構造射。 -/
def weightFunctor (H : I ⥤ SSet.{u}) : (I ⥤ SSet.{u})ᵒᵖ ⥤ SSet.{u} where
  obj W := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W.unop H
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre f.unop H
  map_id W := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_id W.unop H
  map_comp f g := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_comp g.unop f.unop H

/-- 概要：単体的な重みと通常の係数からの余単体 cochain。
方針：反対の重み図式と通常の end の反変関手を合成する。
規約：係数や重みの Kan 性は不要。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。二重の end の比較。 -/
def obj (W : SimplicialObject (I ⥤ SSet.{u})) (H : I ⥤ SSet.{u}) :
    CosimplicialObject SSet.{u} := W.rightOp ⋙ weightFunctor H

/-- 概要：点つき cochain の忘却は通常の cochain と自然に同型。
方針：各次数の end の忘却の同型を重みへの自然性で束ねる。
規約：実際の余単体図式の同型。
使われ方：Goerss–Jardine VIII §1、HA §1.4.2。点つき Tot の基礎の計算。 -/
def pointedUnderlyingIso (W : SimplicialObject (I ⥤ SSet.{u}))
    (D : I ⥤ PointedSimplicialSet.{u}) :
    weightedCochains W D ⋙ PointedSimplicialSet.forget ≅
      obj W (D ⋙ PointedSimplicialSet.forget) :=
  NatIso.ofComponents (fun n ↦ PointedWeightedEnd.underlyingIso (W.obj (op n)) D)
    (fun f ↦ PointedWeightedEnd.underlyingIso_preMap (W.map f.op) D)

end

end SerrePositivity.KST.Spectra.UnderlyingWeightedCochains
