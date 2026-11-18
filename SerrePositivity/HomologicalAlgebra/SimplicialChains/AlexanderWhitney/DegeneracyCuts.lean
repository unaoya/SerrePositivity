module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.SimplicialCuts

/-!
# 退化した単体の切断

概要：Berger–Fresse §1.1.4 の AW 成分において、退化が少なくとも一つの因子に残ることを示す。
方針：繰り返された二頂点を含む区間に制限すると、区間からの射が非単射になることを使う。
規約：退化位置 i は i と i+1 の二頂点を同一視する。
使われ方：AW 公式が退化単体を消し、正規化鎖へ降下することを証明する。
-/

@[expose] public section

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory
open scoped _root_.Simplicial

/-- 概要：退化単体の切断は合成した単体圏の射による引き戻し（Berger–Fresse §1.1.4）。
方針：単体集合の関手性を評価する。
規約：切断は退化後の次数 n+1 で行う。
使われ方：切断後の非単射性から正規化生成元の消滅を導く。 -/
lemma cut_σ (X : SSet) {n : ℕ} (i : Fin (n + 1)) (x : X _⦋n⦌)
    (a b : ℕ) (h : a + b ≤ n + 1) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X (X.σ i x) a b h =
      X.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b (n + 1) h ≫ SimplexCategory.σ i).op x := by
  change (X.map (SimplexCategory.σ i).op ≫ X.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b (n + 1) h).op) x = _
  rw [← X.map_comp]
  rfl

/-- 概要：退化位置を内側に含む区間の像は非単射（Berger–Fresse §1.1.4）。
方針：区間中の i−a 番と i−a+1 番の頂点が同じ像を持つことを示す。
規約：i が区間の右端の場合は含めず、二つの頂点を含む場合を扱う。
使われ方：AW 成分の少なくとも一方の因子が正規化で零になることを示す。 -/
lemma segment_degeneracy_not_mono {n : ℕ} (i : Fin (n + 1))
    (a b : ℕ) (h : a + b ≤ n + 1) (ha : a ≤ i.val) (hb : i.val < a + b) :
    ¬Mono (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b (n + 1) h ≫ SimplexCategory.σ i) := by
  rw [SimplexCategory.mono_iff_injective]
  intro hinj
  let j : Fin (b + 1) := ⟨i.val - a, by omega⟩
  let k : Fin (b + 1) := ⟨i.val - a + 1, by omega⟩
  have hj : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b (n + 1) h).toOrderHom j = i.castSucc := by
    apply Fin.ext
    change a + (i.val - a) = i.val
    omega
  have hk : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b (n + 1) h).toOrderHom k = i.succ := by
    apply Fin.ext
    change a + (i.val - a + 1) = i.val + 1
    omega
  have he : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b (n + 1) h ≫ SimplexCategory.σ i).toOrderHom j =
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b (n + 1) h ≫ SimplexCategory.σ i).toOrderHom k := by
    change i.predAbove ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b (n + 1) h).toOrderHom j) =
      i.predAbove ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b (n + 1) h).toOrderHom k)
    rw [hj, hk, Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  have := congrArg Fin.val (hinj he)
  change i.val - a = i.val - a + 1 at this
  omega

/-- 概要：退化単体の AW 切断では前半か後半の少なくとも一つが退化する（Berger–Fresse §1.1.4）。
方針：退化位置が切断点より前か、それ以後かに分ける。
規約：切断点そのものの退化は後半の因子で消える。
使われ方：AW の各次数成分の正規化への降下に用いる。 -/
lemma aw_degeneracy_not_mono {n : ℕ} (i : Fin (n + 1))
    (p q : ℕ) (h : p + q = n + 1) :
    (¬Mono (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap 0 p (n + 1) (by omega) ≫ SimplexCategory.σ i)) ∨
      (¬Mono (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap p q (n + 1) (by omega) ≫ SimplexCategory.σ i)) := by
  by_cases hp : i.val < p
  · exact Or.inl (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segment_degeneracy_not_mono i 0 p (by omega) (by omega) (by omega))
  · exact Or.inr (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segment_degeneracy_not_mono i p q (by omega) (by omega) (by omega))

end SerrePositivity.SimplicialChains.AlexanderWhitney
