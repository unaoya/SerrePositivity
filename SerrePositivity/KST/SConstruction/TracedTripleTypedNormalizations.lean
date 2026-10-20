module
public import SerrePositivity.KST.SConstruction.TracedTriplePairDiamonds
public import SerrePositivity.KST.SConstruction.TracedTripleBinaryGlue
public import SerrePositivity.KST.SConstruction.FixedBoundarySourceCylinderData

/-! # 元の両正規化円柱を型の揃った実辺の間で保持する
概要：前後二射の元の全正規化を、同じ端点を持つ実辺の間の全円柱にする。
方針：段面の全下面の厳密な回収式で、始辺の表示だけを合わせる。
規約：元の全正規化円柱と外側二部分面の全終辺を厳密に保持する。
使われ方：元の六 diamond の両正規化に沿う全三角形移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 前二射の同じ全正規化円柱を、指定済みの同じ第一補正辺から出る型へ移す。 -/
def monicKTracedTripleFirstTypedNormalization (n : ℕ) :=
  fixedBoundarySourceCylinderData (monicKTracedTripleFirstStageEdgeData F f g h n).first
    (monicKTracedTripleFirstPairBinaryGlue F f g h n)
    (monicKTracedTripleFirstStageEdgeData F f g h n).first_map
    (monicKTracedTripleFirstPairBinaryGlue_relative F f g h n)

/-- 後二射の同じ全正規化円柱も、指定済みの同じ第一補正辺から出る型へ移す。 -/
def monicKTracedTripleLastTypedNormalization (n : ℕ) :=
  fixedBoundarySourceCylinderData (monicKTracedTripleLastStageEdgeData F f g h n).first
    (monicKTracedTripleLastPairBinaryGlue F f g h n)
    (monicKTracedTripleLastStageEdgeData F f g h n).first_map
    (monicKTracedTripleLastPairBinaryGlue_relative F f g h n)

/-- 前二射の全円柱は元の同じ全正規化を厳密に保持する。 -/
lemma monicKTracedTripleFirstTypedNormalization_h (n : ℕ) :
    (monicKTracedTripleFirstTypedNormalization F f g h n).cylinder.homotopy.h =
      (monicKTracedTripleFirstPairNormalization F f g h n).h :=
  (monicKTracedTripleFirstTypedNormalization F f g h n).cylinder_h.trans
    (monicKTracedTripleFirstPairBinaryGlue_h F f g h n)

/-- 後二射の全円柱も元の同じ全正規化を厳密に保持する。 -/
lemma monicKTracedTripleLastTypedNormalization_h (n : ℕ) :
    (monicKTracedTripleLastTypedNormalization F f g h n).cylinder.homotopy.h =
      (monicKTracedTripleLastPairNormalization F f g h n).h :=
  (monicKTracedTripleLastTypedNormalization F f g h n).cylinder_h.trans
    (monicKTracedTripleLastPairBinaryGlue_h F f g h n)

end SerrePositivity.KST.SConstruction
