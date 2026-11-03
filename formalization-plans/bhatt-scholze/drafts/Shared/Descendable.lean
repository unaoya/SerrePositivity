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

/-- 概要：一般形（W9-II-13、**入口を確定：11-03、BS-D3 の D3-04**）：CAlg_A の射 f : R → B（R は一般に離散でない E∞-A 代数、例 Δ_T）が descendable ⇔
Mod_R(D(A)) の中で B の生成する thick ⊗-ideal が R を含む（[Mat16, Def 3.18] を 𝒞 = Mod_R に適用）。離散環版 `IsDescendable` は R = 単位対象の特殊化。
方針：Mod_R(D(A))（E∞ 代数 R 上の加群の安定 ∞ 圏）とその thick ⊗-ideal は基盤側（M15。EInfinity に加群の ∞ 圏がなければ Derived/ に下ろして作る）。
A5 はこの Prop と下の API だけを使い、Mod_R の構成には触れない。
規約：R・B は `(CAlg_R A) _⦋0⦌`、f は `SSet.Edge R B`。完備版（Lemma 8.6 の D_comp(A)）は R・B が完備な対象のときの同じ定義（(h)）。
使われ方：Lemma 8.6（A5-3：R = Δ_T、B = Δ_{T_∞}）、A5-4 の降下。 -/
def IsDescendableOver (R B : (CAlg_R A) _⦋0⦌) (f : SSet.Edge R B) : Prop := sorry -- 基盤待ち（M15）：Mod_R(D(A)) の thick ⊗-ideal

/-- 概要：一般形の index ≤ n：F := fib(R → B)（Mod_R の対象）について F^{⊗_R n} → R が Mod_R で零（[BS17, §11.2]）。
方針：Mod_R の相対テンソルと fiber。
規約：基盤待ち。
使われ方：(d)(f)(g) の一般形。 -/
def HasDescentIndexLEOver (R B : (CAlg_R A) _⦋0⦌) (f : SSet.Edge R B) (n : ℕ) : Prop := sorry -- 基盤待ち（M15）

/-- 概要：(d) の一般形：descendable ⇔ ∃ n, index ≤ n。 -/
theorem isDescendableOver_iff_exists_index (R B : (CAlg_R A) _⦋0⦌) (f : SSet.Edge R B) :
    IsDescendableOver A R B f ↔ ∃ n, HasDescentIndexLEOver A R B f n := by sorry -- 基盤待ち

/-- 概要：離散環版との一致：R が CAlg_A の単位対象（A の埋め込み）で f が B の構造射なら `IsDescendableOver A R B f ↔ IsDescendable A B`。
方針：Mod_{1} = D(A)。主張の形は CAlg_A の単位対象と構造射の名前が決まってから。
規約：基盤待ち。 -/
theorem isDescendableOver_unit_iff : True := by trivial -- 基盤待ち

/-- 概要：(a) の一般形：f : R → B descendable、g : R → R′ なら R′ → B ⊔_R R′（CAlg_A の押し出し＝相対テンソル B ⊗_R R′）も descendable（index も保つ）。
方針：Mod_R → Mod_{R′} の底変換は thick ⊗-ideal を保つ。押し出しの名前は A7 `relativeTensor` の E∞ 版（基盤待ち）。
規約：基盤待ち。A5-4 の降下（Δ_T → Δ_S に沿う底変換）で使う。 -/
theorem isDescendableOver_pushout : True := by trivial -- 基盤待ち

/-- 概要：(b)(c) の一般形：合成と相対テンソル。合成の辺の指定（quasicategory の合成の証人）は基盤の名前が決まってから。 -/
theorem isDescendableOver_comp : True := by trivial -- 基盤待ち
theorem isDescendableOver_tensor : True := by trivial -- 基盤待ち

/-- 概要：(e) の一般形 [Mat16, Prop 3.22]：f : R → B descendable なら任意の R 加群 M について M ≃ Tot(M ⊗_R B^{⊗_R (•+1)})。A5-4 では M = R = Δ_T。
方針：index n で Tot_{≤n} の塔が分裂。Tot は HomotopyLimits（S3 と同じ）。
規約：基盤待ち。 -/
theorem isDescendableOver_tot_equiv : True := by trivial -- 基盤待ち

/-- 概要：(f) の一般形：F := fib(R → B)、RHom_R(F^{⊗_R 2}, R) ∈ D^{≤−1}（Mod_R の内部 Hom。A5 StrongDescent の RHom_{Δ_T}）なら F^{⊗_R 2} → R は零で index ≤ 2。
方針：π_0 RHom = 0。
規約：基盤待ち。Lemma 8.6 の n = 1 で使う。 -/
theorem hasDescentIndexLEOver_two_of_rhom : True := by trivial -- 基盤待ち

/-- 概要：(g)(h) の一般形：Frobenius 余極限（[BS17, Lemma 11.22]、index ≤ n ⇒ colim_φ で ≤ 2n）と完備版（完備な R・B で同じ定義）。 -/
theorem hasDescentIndexLEOver_frobeniusColimit : True := by trivial -- 基盤待ち
theorem isDescendableOver_complete : True := by trivial -- 基盤待ち

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
