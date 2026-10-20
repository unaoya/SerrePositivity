module
public import SerrePositivity.KST.SConstruction.TracedTripleOuterBinaryData

/-! # 外側の移送でも元の全二部分面と全正規化円柱を保持する
概要：両移送円柱の終端と指定側面を、元の全二部分面・元の全正規化へ照合する。
方針：全三角形移送の終端式と全側面式を元の同じ端点表示へ合わせる。
規約：全対角辺は全時刻固定し、元の全二単体を点ごとの等式に弱めない。
使われ方：六対角面の実消去が元の十二面と全円柱を保持することの確認。
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

/-- 左移送の終端は元の同じ全二部分面そのもの。 -/
lemma monicKTracedTripleLeftBinaryTransportComparison_original (n : ℕ) :
    SSet.ι₁ ≫ (monicKTracedTripleLeftBinaryTransportComparison F f g h n).h =
      SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F (f ≫ g) h n).simplex :=
  (monicKTracedTripleLeftBinaryTransportComparison F f g h n).h₁.trans
    (monicKTracedTripleLeftBinaryEdgeData F f g h n).realization_eq

/-- 右移送の終端も元の同じ全二部分面そのもの。 -/
lemma monicKTracedTripleRightBinaryTransportComparison_original (n : ℕ) :
    SSet.ι₁ ≫ (monicKTracedTripleRightBinaryTransportComparison F f g h n).h =
      SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F f (g ≫ h) n).simplex :=
  (monicKTracedTripleRightBinaryTransportComparison F f g h n).h₁.trans
    (monicKTracedTripleRightBinaryEdgeData F f g h n).realization_eq

/-- 左移送の下面は元の同じ前二射全正規化円柱。 -/
lemma monicKTracedTripleLeftBinaryTransportComparison_normalization (n : ℕ) :
    (stdSimplex.δ 2 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleLeftBinaryTransportComparison F f g h n).h =
      (monicKTracedTripleFirstPairNormalization F f g h n).h := by
  rw [monicKTracedTripleLeftBinaryTransportComparison, triangleEdgeTransportComparison_face]
  exact monicKTracedTripleFirstTypedNormalization_h F f g h n

/-- 右移送の上面は元の同じ後二射全正規化円柱。 -/
lemma monicKTracedTripleRightBinaryTransportComparison_normalization (n : ℕ) :
    (stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleRightBinaryTransportComparison F f g h n).h =
      (monicKTracedTripleLastPairNormalization F f g h n).h := by
  rw [monicKTracedTripleRightBinaryTransportComparison, triangleEdgeTransportComparison_face]
  exact monicKTracedTripleLastTypedNormalization_h F f g h n

/-- 左移送では元の共有全対角辺を全比較時刻で厳密に固定する。 -/
lemma monicKTracedTripleLeftBinaryTransportComparison_diagonal (n : ℕ) :
    (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleLeftBinaryTransportComparison F f g h n).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleLeftBinaryEdgeData F f g h n).direct.edge := by
  rw [monicKTracedTripleLeftBinaryTransportComparison, triangleEdgeTransportComparison_face]
  rfl

/-- 右移送でも元の共有全対角辺を全比較時刻で厳密に固定する。 -/
lemma monicKTracedTripleRightBinaryTransportComparison_diagonal (n : ℕ) :
    (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleRightBinaryTransportComparison F f g h n).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleRightBinaryEdgeData F f g h n).direct.edge := by
  rw [monicKTracedTripleRightBinaryTransportComparison, triangleEdgeTransportComparison_face]
  rfl

end SerrePositivity.KST.SConstruction
