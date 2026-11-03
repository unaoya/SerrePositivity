-- 将来の置き場所：SerrePositivity.EInfinity.Descendable.*（新設。調整役の決定、main 86acd98db、M15。E∞ を使わない thick ⊗-ideal・index・安定性は Derived/ へ下ろしてよい。時期・担当は段 G、A5 の中身の段階で）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §2.4、G-A5-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.EInfinity.BarrattEccles.CAlg

/-!
# descendability（[Mat16, Def 3.18]、[BS17, §11.2]）

## 概要
可換環 A 上の E∞ 代数 B（CAlg_A の対象、射 A → B）が descendable とは、D(A) の中で B の生成する thick ⊗-ideal（有限余極限・retract・shift・
任意の対象とのテンソルで閉じた最小の充満部分圏）が単位 A を含むこと。index は fib(A → B)^{⊗n} → A が零になる最小の n。
性質：(a) 底変換、(b) 合成、(c) テンソル、(d) index による判定、(e) 降下 M ≃ Tot(M ⊗_A B^{⊗•+1})（[Mat16, Prop 3.22]）、
(f) RHom_A(F^{⊗2}, A) ∈ D^{<0} ⇒ index ≤ 2、(g) [BS17, Lemma 11.22]（φ と両立する index ≤ n の colim_φ は index ≤ 2n）、(h) 完備版。

## 方針
定義は原典の引用どおり [Mat16] の thick ⊗-ideal（決定 2、D49）。index の判定 (d) は定理。(e) は Tot の塔の分裂（fib^{⊗n} → A 零 ⇒
Amitsur 複体の部分 Tot が retract）。

## 規約
D(A) は `derivedInfinityCategory A`、テンソルは導来テンソル。完備版 (h) は D_comp(A) の完備テンソルで同じ定義。

## 使われ方
Lemma 8.6（A5-3）、Prop 8.5 の降下（A5-4）。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.EInfinity

variable (A : Type u) [CommRing A]

/-- 概要：D(A) の充満部分圏（頂点の述語）が thick ⊗-ideal：有限余極限・retract・shift・任意の対象とのテンソルで閉じる。
方針：述語の閉性の構造。
規約：`(derivedInfinityCategory A) _⦋0⦌ → Prop`。
使われ方：`thickTensorIdealGenerated`。 -/
structure IsThickTensorIdeal (P : (derivedInfinityCategory A) _⦋0⦌ → Prop) : Prop where
  finiteColimits : True
  retracts : True
  shifts : True
  tensor : True

/-- 概要：対象 M の生成する thick ⊗-ideal（M を含む thick ⊗-ideal の sInf）。
方針：述語の ∀ による交わり。
規約：—
使われ方：`IsDescendable`。 -/
def thickTensorIdealGenerated (M : (derivedInfinityCategory A) _⦋0⦌) : (derivedInfinityCategory A) _⦋0⦌ → Prop :=
  fun N => ∀ P, IsThickTensorIdeal A P → P M → P N

/-- 概要：[Mat16, Def 3.18]：A → B（CAlg_A の対象 B）が descendable ⇔ B の生成する thick ⊗-ideal が単位 A を含む。
方針：定義どおり。
規約：B は `(CAlg_R A) _⦋0⦌`、底の D(A) 対象は忘却。**W9-II-13**：これは離散環 A を底とする特殊化。Lemma 8.6 の Δ_T → Δ_{T_∞} は E∞ 代数 Δ_T を底とする
射なので、一般形は「対称モノイダルな安定 ∞ 圏 𝒞 の可換代数対象 B と Mod_B(𝒞) の thick ⊗-ideal」で定義する（`IsDescendableOver`、下）。
使われ方：以下すべて。 -/
def IsDescendable (B : (CAlg_R A) _⦋0⦌) : Prop := sorry -- thickTensorIdealGenerated A (U B) (unit)

/-- 概要：一般形（W9-II-13）：対称モノイダルな安定 ∞ 圏 𝒞（D_comp(A)、Mod_{Δ_T}(D_comp(A)) など）の可換代数対象の射 B → B′ が descendable ⇔
Mod_B(𝒞) で B′ の生成する thick ⊗-ideal が B を含む。離散環版 `IsDescendable` はこの特殊化。
方針：𝒞 と Mod_B の形は EInfinity の `CAlg`／加群の ∞ 圏に合わせる（要確認）。
規約：中身の段階で底の型を変える（実装計画に記録）。
使われ方：Lemma 8.6（A5-3）、A5-4。 -/
def IsDescendableOver : True := trivial

/-- 概要：index ≤ n：fib(A → B)^{⊗n} → A が零（[BS17, §11.2]）。
方針：fib と導来テンソル冪。
規約：—
使われ方：(d)(f)(g)。 -/
def HasDescentIndexLE (B : (CAlg_R A) _⦋0⦌) (n : ℕ) : Prop := sorry

/-- 概要：(d) descendable ⇔ ∃ n, index ≤ n（[Mat16, Prop 3.? / BS17 Lemma 11.?]）。
方針：⇐：fib^{⊗n} → A 零なら A は B ⊗ (−) の有限個の拡大の retract。⇒：thick ⊗-ideal の生成の帰納。
規約：—
使われ方：(f)(g) から descendable へ。 -/
theorem isDescendable_iff_exists_index (B : (CAlg_R A) _⦋0⦌) : IsDescendable A B ↔ ∃ n, HasDescentIndexLE A B n := by sorry

/-- 概要：(a) 底変換：A → B descendable、A → A′ なら A′ → B ⊗_A A′ descendable（index も保つ）。 -/
theorem isDescendable_baseChange : True := by trivial

/-- 概要：(b) 合成：A → B、B → C descendable なら A → C。 -/
theorem isDescendable_comp : True := by trivial

/-- 概要：(c) テンソル：A → B、A → C descendable なら A → B ⊗_A C（(a) と (b)）。 -/
theorem isDescendable_tensor : True := by trivial

/-- 概要：(e) 降下 [Mat16, Prop 3.22]：A → B descendable なら ∀ M ∈ D(A)、M ≃ Tot(M ⊗_A B^{⊗•+1})（Amitsur 複体の全化）。
方針：index n で Tot_{≤n} の塔が分裂。
規約：Tot は HomotopyLimits の全化（S3 の Tot と同じ）。
使われ方：A5-4 の降下。 -/
theorem isDescendable_tot_equiv : True := by trivial

/-- 概要：(f) F := fib(A → B)。RHom_A(F^{⊗2}, A) ∈ D^{<0} なら F^{⊗2} → A は零、よって index ≤ 2。
方針：π_0 RHom = 0。
規約：—
使われ方：Lemma 8.6 の n = 1。 -/
theorem hasDescentIndexLE_two_of_rhom : True := by trivial

/-- 概要：(g) [BS17, Lemma 11.22]：A → B が index ≤ n で両者に両立する自己準同型 φ があれば、colim_φ A → colim_φ B は index ≤ 2n。
方針：BS17 の議論（余極限の fib のテンソル冪の零性）。
規約：sequential 余極限。
使われ方：Lemma 8.6 の perf 版。 -/
theorem hasDescentIndexLE_frobeniusColimit : True := by trivial

/-- 概要：(h) 完備版：D_comp(A) で完備テンソルについて同じ定義と (a)〜(g)。原典 Lemma 8.6 の形。
方針：完備化は対称モノイダルな局所化。
規約：—
使われ方：Lemma 8.6。 -/
theorem isDescendable_complete : True := by trivial

/-- 概要：忠実平坦なら descendable（[Mat16, Prop 3.31]）。記録（A5 では直接使わない）。 -/
theorem isDescendable_of_faithfullyFlat : True := by trivial

end SerrePositivity.EInfinity
