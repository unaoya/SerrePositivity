-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.CechAlexander（仮。原典 §4.3 Constr 4.17・4.18、Rem 4.19）
-- 設計書：formalization-plans/bhatt-scholze/a0-design.md §2.8、単位 A0-2。基準コミット 972bb7f53。ビルドしない。
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Products
-- 本ファイルは drafts/A0/PrismaticSite.lean・PrismaticEnvelope.lean と drafts/Sheaves/CechConerveLimit.lean を import する。

/-!
# Čech–Alexander 複体（BS 著者版 Construction 4.17・4.18、Remark 4.19）

## 概要
p 完備な A/d 代数 R について、原典 Construction 4.18 の strictly functorial な選び方（B₀ = R の台集合上の多項式環の (p,d) 完備化）で
Čech–Alexander の余単体的対象 C^• ∈ (R/A)_Δ を定義する。C^0 が弱始対象（site では弱終）であること、C^• が C^0 の余積による
Čech 脈体であること、そして（∞ 層の層の S3 と Cor 3.12 により）C^• の Tot が Δ_{R/A} を計算することを主張する。
Rem 4.19 の affine 空間の小さい模型 B₀ = A⟨X_1,…,X_r⟩ と、その prism の底変換との両立も述べる。

## 方針
Čech 余脈体は変数の添字で直接書く：B₀^n = A[X_{|R| × [n]}]^∧、余単体的構造は [m] → [n] から誘導される添字の写像（決定 11-02、設計書 D23）。
各項の envelope は `IsPrismaticEnvelope` の普遍性で選ぶ（Prop 3.13 の適用。存在は多項式代数の R について A0-3c の定理）。
余単体的構造の射は envelope の普遍性（lift）で与える。

## 規約
定義は任意の p 完備 A/d 代数 R について、envelope の存在を仮定（`HasEnvelopes`）して入れる。定理（弱始性、余積、Δ の計算、底変換）は
多項式代数 R について。Tot は Mathlib の `alternatingCofaceMapComplex`（非正規化）を主にし、D(A) の Δ 上の極限との一致は G10。

## 使われ方
Not 4.16 の Δ_{R/A} の計算、Lemma 4.20（底変換）、A1（Thm 5.2 で φ_A^*C^• と pd 包の Čech 複体を比べる、Prop 6.2）、A2（Construction 7.6 の
左 Kan 延長は多項式代数上の C^• から）、κ 不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.DerivedCompletion

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)
variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R]

/-! ## Čech 余脈体の添字（B₀^n = A[X_{|R| × [n]}]^∧） -/

/-- 概要：n 項目の変数の集合 |R| × [n]。
方針：台集合 R と `Fin (n+1)` の積。余単体的構造は第二成分の写像から。
規約：原典の B₀^{⊗(n+1)} の変数。
使われ方：`cechPolynomial`、`cechFreeDelta`。 -/
abbrev cechIndex (n : ℕ) : Type u := R × Fin (n + 1)

/-- 概要：[m] → [n] が誘導する添字の写像 |R| × [m] → |R| × [n]。
方針：第二成分に `θ.toOrderHom`。
規約：余単体的（共変）。
使われ方：余単体的構造の射。 -/
def cechIndexMap {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) : cechIndex R m → cechIndex R n :=
  fun x => (x.1, θ.toOrderHom x.2)

/-- 概要：完備化した自由 δ-A 代数 B^n = A{X_{|R| × [n]}}^∧（原典の Free_{δ,A}(B₀^n)^∧）。
方針：`completedFreeDelta`。
規約：—
使われ方：envelope の始域。 -/
abbrev cechFreeDelta (n : ℕ) : Type u := completedFreeDelta P (cechIndex R n)

/-- 概要：B^m → B^n（θ : [m] → [n] から）。
方針：自由 δ 環の普遍性（変数を `cechIndexMap θ` で送る）と完備化の普遍性。
規約：δ 射。関手性は別の補題。
使われ方：余単体的構造。 -/
def cechFreeDeltaMap {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) : cechFreeDelta P R m →+* cechFreeDelta P R n :=
  sorry -- existsUnique_relativeFreeDeltaHom と existsUnique_deltaPDCompletionHom

/-- 概要：B₀^n = A[X_{|R| × [n]}] から R への評価 X_{(r,i)} ↦ r（原典の全射 B₀ → R の Čech 脈体の項）。
方針：A/d 代数として R を A 代数と見て `MvPolynomial.aeval`。
規約：全射（r = X_{(r,0)} の像）。
使われ方：J₀^n。 -/
def cechEval (n : ℕ) : MvPolynomial (cechIndex R n) A →+* R :=
  letI : Algebra A R := ((algebraMap (A ⧸ P.ideal) R).comp (Ideal.Quotient.mk P.ideal)).toAlgebra
  (MvPolynomial.aeval (fun x : cechIndex R n => x.1)).toRingHom

/-- 概要：原典 Constr 4.17 の J = ker(B → (B/J₀B)^∧)（J₀ = ker(B₀ → R)、完備化は**導来** p 完備化の H⁰）。
方針：J₀ の B^n での像の生成するイデアル J₀B^n について、B^n → (B^n ⧸ J₀B^n)^∧_p の核。
規約：J ⊇ (d)（R は A/d 代数なので d ∈ J₀）。古典的な p 進閉包ではなく導来完備化で取る：普遍性の標的 D は有界でないので D/dD は
p 進分離とは限らないが導来 p 完備ではあり、B/J₀B → D/dD が完備化を経由する（a0-design §5.1 の 2 の注意）。
使われ方：envelope の J。
要確認：一変数の導来 p 完備化 H⁰ の環（E3 の `completionRing` が包んでいる一変数 Koszul 完備化）を使う。`PDCompletionH0 _ p 0` は使わない。 -/
def cechKernel (n : ℕ) : Ideal (cechFreeDelta P R n) :=
  sorry -- RingHom.ker (B^n → 一変数 p 完備化 H⁰ (B^n ⧸ J₀B^n))

lemma generator_mem_cechKernel (n : ℕ) :
    completedFreeDeltaBase P (cechIndex R n) P.generator ∈ cechKernel P R n := by
  sorry

/-! ## envelope の選択（Prop 3.13 の適用） -/

/-- 概要：各項 (B^n, J^n) の envelope が存在するという仮定（Prop 3.13 の適用可能性）。
方針：定義は仮定として持ち、多項式代数の R については A0-3c の定理で供給する。
規約：原典の「Applying Proposition 3.13 yields」に対応。
使われ方：`cechAlexanderObj`。 -/
def HasEnvelopes : Prop :=
  ∀ n : ℕ, ∃ (C : Type u) (_ : CommRing C) (Q : OrientedPrism p C) (η : cechFreeDelta P R n →+* C),
    IsPrismaticEnvelope P (completedFreeDeltaStructure P _) (completedFreeDeltaBase P _)
      (completedFreeDeltaBase_isDeltaHom P _) (cechKernel P R n) (generator_mem_cechKernel P R n) Q η ∧
    IsBoundedPrism Q

/-- 概要：多項式代数 R = (A/d)⟨X_T⟩ では envelope が存在する（Ex 3.14 の場合）。
方針：J₀B は、A/d → A の集合論的切断で係数を持ち上げた変数変換により「変数の部分集合 ＋ (d)」になる（a0-design §2.5、紙の検証 2）。
`exists_prismaticEnvelope_of_variables` と `IsPrismaticEnvelope.of_closure`。
規約：T は任意の集合（有限でなくてよい）。
使われ方：Constr 4.18 の定理の範囲。 -/
theorem hasEnvelopes_of_polynomial (T : Type u)
    (hR : True) : -- 要確認：R ≃ (A/d)⟨X_T⟩（p 完備化した多項式代数）の述べ方
    HasEnvelopes P R := by
  sorry -- 変数変換 ＋ exists_prismaticEnvelope_of_variables

variable (h : HasEnvelopes P R) (κ : Cardinal.{u}) (hκ : cutoff P R ≤ κ)

/-- 概要：Čech–Alexander の n 項目の対象 C^n ∈ (R/A)_Δ（環の側）。
方針：`HasEnvelopes` から envelope を選び、R → C^n/dC^n は B₀^n → R の持ち上げから。濃度は `cardinal_envelope_le` で ≤ κ。
規約：選択を含む（普遍対象なので同型を除いて一意）。
使われ方：余単体的対象 `cechAlexander`。 -/
def cechAlexanderObj (n : ℕ) : PrismOver P R κ :=
  sorry -- Classical.choose (h n) から組み立てる

/-- 概要：余単体的対象 C^• : Δ ⥤ PrismOver P R κ（原典 Constr 4.18）。
方針：θ : [m] → [n] に `cechFreeDeltaMap θ` を envelope の普遍性で C^m → C^n に延ばす。関手性は lift の一意性。
規約：`CosimplicialObject (PrismOver P R κ)`。
使われ方：Tot、弱始性、余積、Δ の計算。 -/
def cechAlexander : CosimplicialObject (PrismOver P R κ) where
  obj n := cechAlexanderObj P R h κ hκ n.len
  map θ := sorry -- envelope の lift
  map_id := by sorry
  map_comp := by sorry

/-! ## 性質（多項式代数の R について） -/

/-- 概要：Constr 4.17：C^0 は (R/A)_Δ の弱始対象（環の側。site では弱終）。
方針：任意の D について B₀ → D を R → D/dD の持ち上げとして選び（多項式環）、δ 構造で B → D に一意に延ばし、envelope の普遍性で C → D。
規約：R に smooth 性は不要（持ち上げは多項式環の普遍性だけ）。
使われ方：S3 の補題の仮定。 -/
theorem cechAlexanderObj_weaklyInitial (D : PrismOver P R κ) :
    Nonempty (cechAlexanderObj P R h κ hκ 0 ⟶ D) := by
  sorry -- Constr 4.17 の証明

/-- 概要：C^n は C^0 の (n+1) 個の余積（Constr 4.17 の最後の文「B₀ のテンソル積を余積に送る」）。
方針：envelope の普遍性と自由 δ 環の普遍性で余積の普遍性を確かめる。
規約：Mathlib の `Cofan` と `IsColimit`。一般の余積の存在は主張しない。
使われ方：S3 の `CechNerveData`（site では積）。 -/
theorem cechAlexander_isCoproduct (n : ℕ) :
    ∃ ι : Fin (n + 1) → (cechAlexanderObj P R h κ hκ 0 ⟶ cechAlexanderObj P R h κ hκ n),
      Nonempty (IsColimit (Cofan.mk (cechAlexanderObj P R h κ hκ n) ι)) := by
  sorry

/-- 概要：C^• の Čech 脈体のデータ（site の側、S3 の入力）。
方針：`cechAlexander` を site（opposite）の単体的対象として読み、`cechAlexander_isCoproduct` の余錐を積の錐にする。
規約：S3 の `CechNerveData`。
使われ方：`cechAlexander_isLimitCone`。
要確認：`PrismOverSmall` への移送（`equivSmallModel`）。 -/
def cechNerveData : True := trivial

/-- 概要：Constr 4.18 ＋ 脚注 10：O_Δ 上の錐が極限錐 ⇔ C^• への制限（Tot）が極限錐。
方針：S3 の `isLimitCone_iff_restrict_cech` に `cechAlexanderObj_weaklyInitial` と `cechNerveData` を渡す。
規約：O_Δ は D(A) 値前層 `structurePresheafDerived`。層化は経由しない（前層の主張）。
使われ方：`prismaticCohomology_eq_cechAlexanderTot`。 -/
theorem cechAlexander_isLimitCone_iff : True := by
  trivial -- 要確認：形状の射 `cechShape` と `structurePresheafDerived` の型が揃ってから述べる

/-- 概要：Δ_{R/A} は Tot O_Δ(C^•) に等しい（Constr 4.18 の主張）。
方針：Cor 3.12(d)（O_Δ は層）で RΓ = Γ(O_Δ)、`derivedGlobalSections_of_isSheaf`、`cechAlexander_isLimitCone_iff`、`exists_limitCone_of_cech`。
規約：等しさは「同じ頂点をもつ極限錐の存在」（E3 の規約）。
使われ方：A1 の計算を Tot で行う根拠。 -/
theorem prismaticCohomology_eq_cechAlexanderTot : True := by
  trivial -- 要確認：同上

/-- 概要：Tot を余鎖複体で表す：余単体的 A 加群 [n] ↦ C^n の交代余面複体（非正規化、Mathlib）。
方針：`CosimplicialObject.alternatingCofaceMapComplex`。
規約：次数 n に C^n。D(A) の Δ 上の極限との一致は G10（別ファイル）。
使われ方：A1 の計算（Thm 5.2、Lemma 5.4、Prop 6.2）。 -/
def cechAlexanderComplex : CochainComplex (ModuleCat.{u} A) ℕ :=
  sorry -- (cechAlexander ⋙ 台の A 加群) に alternatingCofaceMapComplex を当てる

/-- 概要：mod d の複体 C^•/dC^•（Ō_{R/A} を計算する）。
方針：同上、`reducedStructurePresheaf`。
規約：A/d 加群の複体としても読める。
使われ方：A1 の HT 比較。 -/
def cechAlexanderReducedComplex : CochainComplex (ModuleCat.{u} A) ℕ :=
  sorry

/-! ## Rem 4.19：affine 空間の小さい模型 -/

/-- 概要：R = (A/d)⟨X_1,…,X_r⟩ に対する B₀ = A⟨X_1,…,X_r⟩ の小さい模型。C^n は (A{X^{(0)},…,X^{(n)}}^∧, (d, X^{(i)} − X^{(0)})) の envelope。
方針：`exists_prismaticEnvelope_of_variables`（S = Fin r × Fin (n+1)、Z = 差の変数、変数変換後）。
規約：R は p 完備化した多項式代数（有限変数）。
使われ方：Lemma 4.20、Prop 6.2、Thm 5.2 の計算。 -/
def cechAlexanderAffine (r : ℕ) : True := trivial
-- 決定（design-status.md (B)）：R := `MvPolynomial (Fin r) (A ⧸ P.ideal)` の一変数 p 進完備化の H⁰（E3 の `completionRing` と同じ道具）。
-- A1 の `affineAlgebra` と同じ定義にし、`CosimplicialObject (PrismOver P R κ)` として書き直す。

/-- 概要：Rem 4.19 の模型は Constr 4.18 の模型と同じ Δ を計算する（どちらも極限錐）。
方針：両方の C^0 が弱始なので S3 の補題を二度使う。
規約：—
使われ方：計算は小さい模型で、関手性は大きい模型で。 -/
theorem cechAlexanderAffine_computes : True := by trivial

/-- 概要：Rem 4.19 の模型は prism の底変換と可換：(A,(d)) → (A′,(d′)) について項ごとの完備底変換が A′ 側の模型（Prop 3.13(2)）。
方針：`prismaticEnvelope_baseChange_of_variables`。
規約：底変換は prism の射に沿う完備テンソル。
使われ方：Lemma 4.20、Constr 6.1、Prop 6.2。 -/
theorem cechAlexanderAffine_baseChange : True := by trivial

end SerrePositivity.BhattScholze.Prismatic
