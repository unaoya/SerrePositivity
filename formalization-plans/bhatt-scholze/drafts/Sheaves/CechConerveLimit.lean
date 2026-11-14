-- 将来の置き場所：SerrePositivity.InfinityCategories.Sheaves.CechConerveLimit（層 Sheaves）
-- 設計書：formalization-plans/bhatt-scholze/infinity-sheaves-design.md §1（弱終対象による計算）、単位 S3。基準コミット efa846fe8。型検査対象（5∞-0）。
module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalLimitTransfer
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
-- 本ファイルは drafts/Sheaves/SheafCondition.lean（将来 …Sheaves.SheafCondition）を import する。

/-!
# 弱終対象の Čech 脈体による極限の計算（原典 §4.3 脚注 10 の前層版）

## 概要
小さい圏 𝒟 の弱終対象 U（任意の V から U へ射がある）と、各 n で U の (n+1) 個の積として与えられた単体的対象 U_•（Čech 脈体）に
ついて、任意の E 値前層 F の N(𝒟)^op 上の極限は、余単体的対象 [n] ↦ F(U_n) の Δ 上の極限（Tot）に等しい。
主張は「F 上の錐が極限錐 ⇔ Čech 脈体への制限が極限錐」の形（`CofinalLimitTransfer` と同じ形）。

## 方針
𝒟 に一般の有限積があることは仮定せず、U の冪の積の錐（Fan と IsLimit）をデータとして受け取る（2026-11-02 決定。prismatic site の
一般の余積は一般の Prop 3.13 を要するので存在が保証されない）。証明の経路は二つ：(i) 空間値前層で h_U → 1 が効果的エピであることと
Čech 脈体の幾何学的実現（HTT 6.2.3.5 系、G9）、(ii) Bousfield–Kan の余単体的置換と双余単体的対象の extra degeneracy
（Stacks 07JM の前層の場合、基盤の HomotopyLimits の部品）。どちらを採るかは実装の設計で決める。

## 規約
層条件・位相は使わない（純粋に前層の主張）。E の極限の存在は仮定せず、錐の極限性の同値として述べる。Tot を複体で表すときは
Mathlib の `alternatingCofaceMapComplex`（非正規化）を主にし、D(A) の Δ 上の極限との一致は G10（別ファイル）。

## 使われ方
Constr 4.18（Čech–Alexander 複体が Δ_{R/A} を計算する）、Rem 4.19、Prop 8.5（完全 site、E3 の `limitCone` の形へ）、κ 不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Sheaves

variable {𝒟 : Type u} [SmallCategory 𝒟] {E : SSet.{u + 1}} [Quasicategory E]
-- W9-I-04：E3 の添字圏 `PerfUnder_u p S` は対象が Type (u+1) の大きい圏。S3 は「添字圏の対象は大きくてよく、Čech 側（U_• と Tot）は小さい」形でも
-- 述べる必要がある（宇宙を対象・射・値で分ける）。A5-4 の `limit_perfUnder_eq_tot` で使う。中身の段階で `𝒟 : Type (u+1)`・`[Category.{u} 𝒟]` の版を足す。

/-- 概要：弱終対象：任意の対象から射がある。
方針：原典の「弱始対象」は環の圏（site の opposite）での言い方で、site では弱終。
規約：一意性は要求しない。
使われ方：Čech 脈体の補題の仮定。Constr 4.17 の C^0。 -/
def IsWeaklyTerminal (U : 𝒟) : Prop := ∀ V : 𝒟, Nonempty (V ⟶ U)

/-- 概要：U の Čech 脈体のデータ：単体的対象 U_• と、各 U_n を U の (n+1) 個の積として示す錐。
方針：一般の有限積の存在を仮定せず、必要な積だけをデータで持つ。単体的構造の射は射影と両立する（Čech 脈体の条件）。
規約：`Fan` と `IsLimit` は Mathlib の 1 圏のもの。
使われ方：補題の入力。prismatic site では C^• と、余積の普遍性（Constr 4.17 の最後の文）から作る。 -/
structure CechNerveData (U : 𝒟) where
  /-- 単体的対象 U_•。 -/
  obj : SimplicialObject 𝒟
  /-- U_n から U への (n+1) 本の射影。 -/
  proj : ∀ (n : ℕ) (i : Fin (n + 1)), obj.obj (Opposite.op ⦋n⦌) ⟶ U
  /-- 射影が U_n を U^{n+1} の積にする。 -/
  isLimit : ∀ n : ℕ, IsLimit (Fan.mk (obj.obj (Opposite.op ⦋n⦌)) (proj n))
  /-- 単体的構造の射は射影の添字を写す（Čech 脈体の条件）。 -/
  proj_map : ∀ {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)),
    obj.map θ.op ≫ proj m i = proj n (θ.toOrderHom i)

/-- 概要：Čech 脈体の形状の射：N(Δ) → N(𝒟)^op（U_• の rightOp の nerve を持ち上げたもの）。
方針：`SimplicialObject 𝒟 = SimplexCategoryᵒᵖ ⥤ 𝒟` の `rightOp : SimplexCategory ⥤ 𝒟ᵒᵖ`。
規約：始域は持ち上げた N(Δ)（`presheafShape SimplexCategory` = N(Δᵒᵖ) ではない。W9-I-02 で訂正）。Tot の添字は Δ（原典 Constr 4.18・脚注 10）。
使われ方：前層 F をこれに沿って制限すると余単体的対象 [n] ↦ F(U_n)。 -/
def cechShape {U : 𝒟} (d : CechNerveData U) :
    (SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategory) ⟶ presheafShape 𝒟 where
  app _ := ↾fun s => ⟨s.down ⋙ d.obj.rightOp⟩
  naturality _ _ _ := rfl

/-- 概要：脚注 10（前層版）：U が弱終で U_• がその Čech 脈体なら、F 上の錐が極限錐であることと、Čech 脈体への制限が極限錐であることは同値。
方針：§方針 の (i) または (ii)。
規約：錐の頂点はそのまま。E の極限の存在は仮定しない。
使われ方：Constr 4.18、Rem 4.19、Prop 8.5。 -/
theorem isLimitCone_iff_restrict_cech {U : 𝒟} (hU : IsWeaklyTerminal U) (d : CechNerveData U)
    (F : Presheaf 𝒟 E) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c (cechShape d)) := by
  sorry -- G9：効果的エピの Čech 脈体の実現、または Bousfield–Kan との比較

/-- 概要：極限の存在も同値。
方針：上の同値と `restrictJoinCone`。逆向きは Čech 側の極限錐から F 上の錐を延長する（§方針 の経路に含まれる）。
規約：形状は同じ。
使われ方：Tot の存在から Δ_{R/A} の存在（層化を経由しない直接の形）。 -/
theorem hasLimit_iff_cech {U : 𝒟} (hU : IsWeaklyTerminal U) (d : CechNerveData U)
    (F : Presheaf 𝒟 E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (cechShape d ≫ F) := by
  sorry -- 同上。逆向きは錐の延長

/-- 概要：Čech 側の極限錐（Tot）から、同じ頂点をもつ F 上の極限錐を得る。
方針：`hasLimit_iff_cech` の逆向きの構成を頂点つきで述べる。
規約：頂点の等号で述べる（E3 の `vertex_eq` と同じ規約）。
使われ方：Δ_{R/A} ≃ Tot O_Δ(C^•)（`prismaticCohomology_iso_cechAlexanderTot`）。 -/
theorem exists_limitCone_of_cech {U : 𝒟} (hU : IsWeaklyTerminal U) (d : CechNerveData U)
    (F : Presheaf 𝒟 E) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (cechShape d ≫ F)) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone t) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ c.vertex = t.vertex := by
  sorry -- 錐の延長と `isLimitCone_iff_restrict_cech`

/-! ## 大きい添字圏の版（W9-I-04、BS-D3 の D3-02。2026-11-03）

E3 の添字圏 `PerfUnder_u p S`（対象 Type (u+1)、射 Type u）は `SmallCategory` ではない。上の `CechNerveData` と同じ四欄を `[Category.{u} 𝒟]`・`𝒟 : Type (u+1)` で述べ、
Čech 側（U_• と Tot）は小さいままにする。大きい nerve は最初から E と同じ宇宙にある。 -/

section Large
variable {𝒟 : Type (u + 1)} [Category.{u} 𝒟]

/-- 概要：大きい添字圏での弱終対象（小さい版と同じ条件）。 -/
def IsWeaklyTerminalLarge (U : 𝒟) : Prop := ∀ V : 𝒟, Nonempty (V ⟶ U)

/-- 概要：大きい添字圏での Čech 脈体のデータ：小さい版 `CechNerveData` と同じ四欄（U_•、射影、Fan の `IsLimit`、射影と単体的構造射の両立）。
方針：Mathlib の `Fan`・`IsLimit` は宇宙を跨いで使える。U_n 自体は 𝒟 の対象（大きくてよい）。
規約：S3 の大きい版（W9-I-04）。A5 の `perfUnder_cechNerveData` はこれを返す。
使われ方：A5-4 `limit_perfUnder_eq_tot`。 -/
structure CechNerveDataLarge (U : 𝒟) where
  obj : SimplicialObject 𝒟
  proj : ∀ (n : ℕ) (i : Fin (n + 1)), obj.obj (Opposite.op ⦋n⦌) ⟶ U
  isLimit : ∀ n : ℕ, IsLimit (Fan.mk (obj.obj (Opposite.op ⦋n⦌)) (proj n))
  proj_map : ∀ {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)),
    obj.map θ.op ≫ proj m i = proj n (θ.toOrderHom i)

abbrev PresheafLarge (𝒟 : Type (u+1)) [Category.{u} 𝒟] (E : SSet.{u+1}) :=
  nerve 𝒟ᵒᵖ ⟶ E

/-- Δ 側だけを持ち上げる。A5 の largeCechShape と同じく射列に rightOp を適用する。 -/
def cechShapeLarge {U : 𝒟} (d : CechNerveDataLarge U) :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶ nerve 𝒟ᵒᵖ where
  app _ := ↾fun x => (d.obj.rightOp.mapComposableArrows _).obj x.down
  naturality := by sorry -- 射列の制限と関手による像は可換

/-- 大きい添字圏の前層に対する S3。制限の前後で錐の頂点は同じ。 -/
theorem isLimitCone_iff_restrict_cech_large {E : SSet.{u+1}} [Quasicategory E] {U : 𝒟} (hU : IsWeaklyTerminalLarge U)
    (d : CechNerveDataLarge U) (F : PresheafLarge 𝒟 E) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c (cechShapeLarge d)) := by
  sorry -- 各試験対象から U への写像の集合は非空。その Čech 脈体で S3 と同じ極限判定

/-- A5 が受け取るのは Čech 側の錐だけなので、その延長も頂点つきで述べる。 -/
theorem exists_limitCone_of_cech_large {E : SSet.{u+1}} [Quasicategory E] {U : 𝒟} (hU : IsWeaklyTerminalLarge U)
    (d : CechNerveDataLarge U) (F : PresheafLarge 𝒟 E) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (cechShapeLarge d ≫ F))
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone t) : ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ c.vertex = t.vertex := by
  sorry -- Čech の添字関手の始性による錐の延長（G8・G9）

end Large

end SerrePositivity.InfinityCategories.Sheaves
