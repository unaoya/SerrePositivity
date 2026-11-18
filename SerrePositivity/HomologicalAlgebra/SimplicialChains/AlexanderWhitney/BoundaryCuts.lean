module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.FaceCuts
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.ComponentLaws

/-!
# AW 境界計算の単体の公式

概要：Berger–Fresse §1.1.4 の AW 公式と微分の可換性を生成元で計算する準備を行う。
方針：面写像との関係を単体に評価し、正規化生成元の微分を交代和で表す。
規約：自然数の鎖次数を用い、面の符号は (−1)^i とする。
使われ方：AW 成分の境界をテンソル積の微分と比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.AlgebraicTopology
open scoped _root_.Simplicial

private lemma pullback_comp (X : SSet) {k m n : ℕ}
    (f : ⦋k⦌ ⟶ ⦋m⦌) (g : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) :
    X.map f.op (X.map g.op x) = X.map (f ≫ g).op x := by
  change (X.map g.op ≫ X.map f.op) x = _
  rw [← X.map_comp]
  rfl

/-- 概要：除去位置以前に始まらない切断の面公式（Berger–Fresse §1.1.4）。
方針：単体圏の射の等式を反変関手に適用する。
規約：除去位置は区間の始点以前にある。
使われ方：AW 境界の後半の因子を計算する。 -/
lemma cut_δ_before (X : SSet) {n : ℕ} (x : X _⦋n + 1⦌) (i : Fin (n + 2))
    (a b : ℕ) (h : a + b ≤ n) (hi : i.val ≤ a) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X (X.δ i x) a b h = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x (a + 1) b (by omega) := by
  change X.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h).op (X.map (SimplexCategory.δ i).op x) = _
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.pullback_comp, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap_face_before i a b h hi]
  rfl

/-- 概要：区間の終点より後を除く切断の面公式（Berger–Fresse §1.1.4）。
方針：面写像と区間包含の合成が同じ区間包含であることを使う。
規約：除去位置が区間の終点に一致する場合は含まない。
使われ方：AW 境界の前半の因子を計算する。 -/
lemma cut_δ_after (X : SSet) {n : ℕ} (x : X _⦋n + 1⦌) (i : Fin (n + 2))
    (a b : ℕ) (h : a + b ≤ n) (hi : a + b < i.val) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X (X.δ i x) a b h = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x a b (by omega) := by
  change X.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h).op (X.map (SimplexCategory.δ i).op x) = _
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.pullback_comp, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap_face_after i a b h hi]
  rfl

/-- 概要：切断面を長い区間の面として表す公式（Berger–Fresse §1.1.4）。
方針：区間内部の面写像の等式を単体に評価する。
規約：除去位置から区間の始点を引いた番号で面を取る。
使われ方：AW 境界を二つの因子の微分と同定する。 -/
lemma cut_δ_inside (X : SSet) {n : ℕ} (x : X _⦋n + 1⦌) (i : Fin (n + 2))
    (a b : ℕ) (h : a + b ≤ n) (ha : a ≤ i.val) (hb : i.val ≤ a + b + 1) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X (X.δ i x) a b h =
      X.δ (⟨i.val - a, by omega⟩ : Fin (b + 2)) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x a (b + 1) (by omega)) := by
  change X.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h).op (X.map (SimplexCategory.δ i).op x) =
    X.map (SimplexCategory.δ (⟨i.val - a, by omega⟩ : Fin (b + 2))).op
      (X.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a (b + 1) (n + 1) (by omega)).op x)
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.pullback_comp, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.pullback_comp, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap_face_inside i a b h ha hb]

variable (A : Type u) [CommRing A]

private lemma linearization_structure_freeMk (X : SSet.{0})
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (x : X.obj Δ) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X).map f (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (X.map f x)) := ModuleCat.free_map_apply _ _

/-- 概要：一般の単体集合の正規化生成元の微分（Berger–Fresse §1.1.4）。
方針：正規化射影の鎖写像の条件を自由生成元で評価する。
規約：n+1 鎖から n 鎖への微分は全ての面の交代和である。
使われ方：正規化 AW 成分の鎖写像の条件を有限和へ帰着する。 -/
lemma generator_d (X : SSet.{0}) (n : ℕ) (x : X _⦋n + 1⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (n + 1) n (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (n + 1) x) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X n (X.δ i x) := by
  have h := congrArg (fun f => f (ModuleCat.freeMk (ULift.up x)))
    ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A X).comm (n + 1) n)
  change (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (n + 1) n (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (n + 1) x) =
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A X).f n
      (((alternatingFaceMapComplex (ModuleCat A)).obj ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X)).d
        (n + 1) n (ModuleCat.freeMk (ULift.up x))) at h
  rw [h]
  erw [alternatingFaceMapComplex_obj_d]
  simp [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator, SimplicialObject.δ, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.linearization_structure_freeMk]

end SerrePositivity.SimplicialChains.AlexanderWhitney
