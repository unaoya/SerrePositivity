-- 将来の置き場所：SerrePositivity.BhattScholze.Almost.AlmostConnectivity（仮。原典 Prop 10.4 の必要部分、Lemma 10.5、J-almost の基本）
-- 設計書：formalization-plans/bhatt-scholze/a8-design.md §2.1・§3.1、単位 A8-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Almost.PerfectoidAlmost
public import SerrePositivity.BhattScholze.Almost.Lemma103
-- W9-III-08：Lemma103 は現行の CompletedTensor（→ IntegralExistence → Inputs）を import する。2a 後に Lemma103 の依存を E3 非依存の芯（仮称 CompletedTensorCore）へ向ける（a9-design §7）。
-- 本ファイルは drafts/A7/AnimatedPerfectoidization.lean（Prop 8.13）、drafts/DerivedGeneral/{Truncation,CompletionFunctor}.lean を import する。

/-!
# J-almost 連結性（BS 著者版 Prop 10.4 の必要部分、Lemma 10.5）と J-almost の基本

## 概要
R perfectoid、J ⊂ R 導来 p 完備、J_perfd = ker(R → (R/J)_perfd)（既存 `perfectoidIdeal`）。導来 p 完備な複体 M が J-almost 零 ⇔ J_perfd ⊗̂^L M = 0
（Prop 10.4 の必要部分、D66）。Lemma 10.5：M 連結 ⇔ M ⊗̂^L R/J_perfd 連結かつ M が J-almost 連結。基本：J-almost は √J で不変、
J = (f_1..f_r) で J-almost ⇔ ∀i (f_i)-almost、忠実平坦な perfectoid の基底変換 R → R′ で反映（(JR′)_perfd = J_perfd R′）。

## 方針
加群版（B5 の `perfectoidIdeal_completedTensor_isZero_of_isAlmostZero`・`_of_completedTensor_isZero`）を truncation の帰納で有界複体に、
完備性と truncation の極限・余極限で非有界に。Lemma 10.5 は三角形 J_perfd ⊗̂ M → M → (R/J)_perfd ⊗̂ M。基底変換は Prop 8.13。

## 規約
J-almost 零は既存 `IsAlmostZero`（CommutativeAlgebra/Almost/Zero）を J_perfd で。cohomological な添字（連結 = D^{≤0}）。

## 使われ方
Thm 10.9 の J-almost 連結性（A8-2）、Thm 10.11 の帰納（A8-4）。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.BhattScholze.Almost

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p) (J : Ideal R)

/-- 概要：導来 p 完備な複体 M が J-almost 連結 ⇔ H^i(M) が J-almost 零（∀ i > 0）。
方針：既存 `IsAlmostZero` を各コホモロジーに。
規約：D(R) の対象。
使われ方：Lemma 10.5、Thm 10.9。 -/
def IsAlmostConnective : True := trivial

/-- 概要：内部補題（W9-III-10）：B := (R/J)_perfd（perfectoid、R/K、K := J_perfd）について Lemma 10.3 の B ⊗̂^L_R B ≃ B から、忘却
U : D_{p-comp}(B) → D_{p-comp}(R) は完全忠実で、極限と余極限を保つ（通常の忘却は余極限を保ち、両側の完備化は同じ p）。像は安定部分圏で、
有界切り捨て（有限個の拡大）と Postnikov 塔の極限・完備余極限で閉じる。
方針：一般の perfectoid 商の Lemma 10.3（既存 `Lemma103` は単項 g の版なので K = ker(R → B) に一般化する）。完備テンソルが任意の逆極限と可換とは主張しない。
規約：—
使われ方：Prop 10.4 の非有界版。 -/
theorem restrictScalars_perfectoidQuotient_fullyFaithful : True := by trivial

/-- 概要：Prop 10.4 の必要部分（D66）：導来 p 完備な複体 M について、M が J-almost 零（全 H^i）⇔ K ⊗̂^L_R M = 0（K = J_perfd）。
方針：加群版（B5。**単項 g の版**なので一般 J は K に対する補題として一般化、W9-III-10）を truncation の帰納で有界複体へ。非有界：各 H^i(M) は B 加群で U の像、
有界切り捨ても像、τ^{≤m}M を下側の切り捨ての逆極限で、M を完備余極限で復元（Postnikov 完備性と U の極限・余極限保存）して M が像に入る；像の上で
K ⊗̂ B = 0 を係数変更。逆は三角形 K ⊗̂ M → M → B ⊗̂ M。
規約：完備テンソル。D66：圏同値は結論にしないが、証明で完全忠実性・像の閉性は使う。
使われ方：Lemma 10.5。 -/
theorem isAlmostZero_iff_completedTensor_isZero : True := by trivial

/-- 概要：G-A8-1 の系（W9-III-10）：導来 p 完備な M について、M が J-almost 連結 ⇔ K ⊗̂^L_R M が連結。
方針：⇒：Prop 10.4 で K ⊗̂ τ^{>0}M = 0、K ⊗̂ τ^{≤0}M は連結（Lemma 10.5 の証明）。⇐：三角形 K ⊗̂ M → M → B ⊗̂ M で i > 0 の H^i(M) は B 加群 H^i(B ⊗̂ M) に一致。
規約：—
使われ方：下の余極限での閉性、Thm 10.11 の A_λ の段（A8-4）。 -/
theorem isAlmostConnective_iff_completedTensor_connective : True := by trivial

/-- 概要：almost 連結な完備複体は完備 filtered 余極限で閉じる：M_λ が J-almost 連結なら LΛ_p(colim_λ M_λ) も。
方針：上の同値で K ⊗̂ − に移し、完備テンソルは完備余極限を保つ；連結な複体は完備 filtered 余極限で閉じる（通常の filtered 余極限は完全、LΛ_p は D^{≤0} を保つ）。
G-A8-8（perfectoid 性の余極限保存）とは別の補題で、各 M_λ が離散・perfectoid であることは使わない。
規約：—
使われ方：Thm 10.11 の A_λ → T̂_perfd（A8-4）。 -/
theorem isAlmostConnective_completedFilteredColimit : True := by trivial

/-- 概要：Lemma 10.5：p 完備な M ∈ D(R) が連結 ⇔ M ⊗̂^L_R R/J_perfd が連結かつ M が J-almost 連結。
方針：⇒ は ⊗̂ R/J_perfd が連結性を保つ。⇐：三角形 J_perfd ⊗̂ M → M → (R/J)_perfd ⊗̂ M、J_perfd ⊗̂ τ^{>0} M = 0（Prop 10.4）、
J_perfd ⊗̂ τ^{≤0} M 連結。(R/J)_perfd = R/J_perfd（Thm 7.4、既存）。
規約：—
使われ方：Thm 10.11 の帰納（A8-4）。 -/
theorem connective_iff_almost : True := by trivial

/-! ## J-almost の基本（G-A8-2） -/

/-- 概要：J_perfd = (√J)_perfd（(R/J)_perfd は perfectoid で被約、普遍性で (R/J)_perfd = (R/√J)_perfd）。J-almost は √J で不変。
方針：既存の perfectoid の被約性と `IsPerfectoidization` の一意性。
規約：—
使われ方：生成元の取り替え（Thm 10.9）。 -/
theorem perfectoidIdeal_radical : True := by trivial
theorem isAlmostZero_radical : True := by trivial

/-- 概要：J = (f_1,…,f_r) のとき、M が J-almost 零 ⇔ ∀ i, M が (f_i)-almost 零。
方針（W9-III-03 で訂正）：⇐：Q := R/f_1 ⊗̂^L_R ⋯ ⊗̂^L_R R/f_r（animated な完備押し出し）は π_0 Q = R/J だが Q ≠ R/J（p ねじれなしの R、f_1 = f_2 = p で H^{−1} = R/p ≠ 0）。
Prop 8.5 系 4（`perfectoidization_piZero`）で Q_perfd ≃ (R/J)_perfd、Prop 8.13 で (R/J)_perfd ≃ (R/f_1)_perfd ⊗̂_R ⋯（単位と両立）。M が各 (f_i)-almost 零なら
三角形 (f_i)_perfd ⊗̂ M → M → (R/f_i)_perfd ⊗̂ M で M → (R/f_i)_perfd ⊗̂ M は同値、順にテンソルして M → (R/J)_perfd ⊗̂ M が同値、よって J_perfd ⊗̂ M = 0（紙 1）。
⇒：(f_i) ⊂ J から (f_i)_perfd ⊂ J_perfd を各 H^j(M) に。空の生成族は J = 0 で自明。
規約：—
使われ方：Thm 10.9 を一つの生成元に帰着。 -/
theorem isAlmostZero_iff_forall_gen : True := by trivial

/-- 概要：perfectoid の射 R → R′ が p 完備忠実平坦なら (JR′)_perfd = J_perfd R′（(R′/JR′)_perfd = (R/J)_perfd ⊗̂_R R′、Prop 8.13）。
M が J-almost 零 ⇔ M ⊗̂_R R′ が JR′-almost 零。
方針：Prop 8.13（A7-1）、忠実平坦で零性を反映。
規約：—
使われ方：Thm 10.9 で基底を絶対整閉に取り替える。 -/
theorem perfectoidIdeal_baseChange : True := by trivial
theorem isAlmostZero_baseChange_iff : True := by trivial

end SerrePositivity.BhattScholze.Almost
