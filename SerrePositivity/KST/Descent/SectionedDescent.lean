module

public import SerrePositivity.KST.Descent.ReducedDescentStep

/-!
# 切断を持つ射の全次数降下

## 概要
整・被約・一般の帰納を実行し、切断を持ち有限群が点のファイバーで推移的な射の降下を示す。

## 方針
内側では既約成分数の強い帰納、外側では自然数の次元上界の帰納を実行する。

## 規約
自然な blowup 列・有限積保存・冪零不変性は実降下から供給する明示的な条件。
切断を持たない射への Čech 還元は別工程であり、定理 3.1 全体の完成とは区別する。

## 使われ方
論文 定理 3.1 の、補題 3.2 による切断を持つ場合への還元の後に使う段階。
原典の τ 位相の層論を Čech 計算に置き換える全体経路の一部。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent.NaturalBlowupSequences

variable {S : Scheme.{u}} [IsNoetherian S] {Coefficient : Type w}
variable {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
variable (data : NaturalBlowupSequences L) [Nilinvariant S L]
variable [∀ H n, PreservesFiniteProducts (L H n)]
variable {G : Type u} [Group G] [Finite G]

include data

/-- 概要：全ての有限な次元上界について低次元の帰納仮定を実際に構成（論文 定理 3.1）。
方針：空の基底による始点と、整・被約・一般の一段を自然数帰納で結ぶ。
規約：低次元の降下を外部仮定として残さない。
使われ方：任意の指定された有限次元上界に対する切断つき降下。 -/
theorem sectionedDescentBelow (d : ℕ) : SectionedDescentBelow L G d := by
  induction d with
  | zero => exact sectionedDescentBelow_zero L G
  | succ d ih =>
    intro B V _ p action over_base s hs transitive bound
    apply data.piDescent_of_below p action over_base s hs transitive d _ ih
    apply ENat.WithBot.lt_add_one_iff.mp
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using bound

/-- 概要：切断を持つ点のファイバーで推移的な射の全次数降下（論文 定理 3.1）。
方針：二つの帰納を完了した結果を、指定された有限な次元上界へ適用する。
規約：中心・閉和・低次元の局所降下を独立した仮定に残さない。
使われ方：Čech 還元で切断を得た各項の指定比較。 -/
theorem sectioned_piDescent {B V : FiniteTypeSchemes S} [IsSeparated V.obj.hom]
    (p : V ⟶ B) (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (s : B ⟶ V) (hs : s ≫ p = 𝟙 B)
    (transitive : ∀ x y : V.obj.left, p.hom.left x = p.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (d : ℕ) (bound : topologicalKrullDim B.obj.left ≤ d) : L.PiDescent p action over_base :=
  data.piDescent_of_below p action over_base s hs transitive d bound (data.sectionedDescentBelow d)

end SerrePositivity.KST.Descent.NaturalBlowupSequences
