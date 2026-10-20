module
public import SerrePositivity.KST.SConstruction.TracedCompositeBinaryFaces
public import SerrePositivity.KST.SConstruction.TracedBFTriplePairNormalizations

/-! # 元の二段三角形を外側の実二部分三角形へ貼る全円柱
概要：前二射・後二射の元の補正辺を、外側の二部分三角形の同じ補正面へ全端点固定で移す。
方針：元の全正規化円柱を保持し、両端の全区間を同じ全三角形の面へ表示移送する。
規約：元の両三角形と全円柱を変更せず、全区間境界を全比較時刻で固定する。
使われ方：三入力の四面と元の実交換面を同じ全補正辺路に沿って貼り合わせる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の前二射三角形の下面から、左外側二部分三角形の下面への同じ全正規化円柱。 -/
def monicKTracedTripleFirstPairBinaryGlue (n : ℕ) :=
  familyHomotopyEndpointTransport (monicKTracedTripleFirstPairNormalization F f g h n)
    (monicKTracedTripleFirstPairStageTriangle_first F f g h n)
    (monicKPrismCompositeBinaryPointTriangle_first F (f ≫ g) h n).symm

/-- 全貼り合わせ円柱は元の同じ正規化円柱そのもの。 -/
lemma monicKTracedTripleFirstPairBinaryGlue_h (n : ℕ) :
    (monicKTracedTripleFirstPairBinaryGlue F f g h n).h =
      (monicKTracedTripleFirstPairNormalization F f g h n).h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 左貼り合わせは元の全区間境界を全比較時刻で厳密に固定する。 -/
lemma monicKTracedTripleFirstPairBinaryGlue_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleFirstPairBinaryGlue F f g h n).h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫ stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairStageTriangle F f g h n).simplex := by
  rw [monicKTracedTripleFirstPairBinaryGlue_h, monicKTracedTripleFirstPairNormalization_relative,
    monicKTracedTripleFirstPairStageTriangle_first]

/-- 元の後二射三角形の下面から、右外側二部分三角形の上面への同じ全正規化円柱。 -/
def monicKTracedTripleLastPairBinaryGlue (n : ℕ) :=
  familyHomotopyEndpointTransport (monicKTracedTripleLastPairNormalization F f g h n)
    (monicKTracedTripleLastPairStageTriangle_first F f g h n)
    (monicKPrismCompositeBinaryPointTriangle_second F f (g ≫ h) n).symm

/-- 右の全貼り合わせ円柱も元の同じ正規化円柱そのもの。 -/
lemma monicKTracedTripleLastPairBinaryGlue_h (n : ℕ) :
    (monicKTracedTripleLastPairBinaryGlue F f g h n).h =
      (monicKTracedTripleLastPairNormalization F f g h n).h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 右貼り合わせも元の全区間境界を全比較時刻で厳密に固定する。 -/
lemma monicKTracedTripleLastPairBinaryGlue_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleLastPairBinaryGlue F f g h n).h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫ stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleLastPairStageTriangle F f g h n).simplex := by
  rw [monicKTracedTripleLastPairBinaryGlue_h, monicKTracedTripleLastPairNormalization_relative,
    monicKTracedTripleLastPairStageTriangle_first]

end SerrePositivity.KST.SConstruction
