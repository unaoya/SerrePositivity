-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.CechAlexander（仮。原典 §4.3 Constr 4.17・4.18、Rem 4.19）
-- 設計書：formalization-plans/bhatt-scholze/a0-design.md §2.8、単位 A0-2。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeConstruction
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.BhattScholze.Prismatic.AffinePolynomial

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Products
-- 本ファイルは drafts/A0/PrismaticSite.lean・PrismaticEnvelope.lean・FlatDescent.lean と drafts/Sheaves/CechConerveLimit.lean を import する。

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
universe u v
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.DerivedCompletion SerrePositivity.InfinityCategories


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
一変数の標準射とその核は `envelopeClosure`。 -/
def cechKernel (n : ℕ) : Ideal (cechFreeDelta P R n) :=
  let ι := (pdCompletionUnit (RelativeFreeDeltaRing (R := A) (cechIndex R n)) p
    (algebraMap A _ P.generator)).comp (relativeFreeInitialPolynomialMap (cechIndex R n) A).toRingHom
  envelopeClosure p ((RingHom.ker (cechEval P R n)).map ι)

lemma generator_mem_cechKernel (n : ℕ) :
    completedFreeDeltaBase P (cechIndex R n) P.generator ∈ cechKernel P R n := by
  sorry -- 評価で d は零なので延長イデアルに入り、le_envelopeClosure を適用する

/-! ## envelope の選択（Prop 3.13 の適用） -/

/-- 概要：各項 (B^n, J^n) の envelope が存在し、有界で、**濃度 ≤ cutoff** であるという仮定（Prop 3.13 の適用可能性）。
方針：定義は仮定として持ち、多項式代数の R については A0-3c の定理で供給する（濃度は変数模型との一意同型で `cardinal_envelope_le` から移す）。
規約：原典の「Applying Proposition 3.13 yields」に対応。濃度の条件は W9-I-12（一般の `HasEnvelopes` だけからは envelope の濃度を評価できない）で追加。
使われ方：`cechAlexanderObj`。 -/
def HasEnvelopes : Prop :=
  ∀ n : ℕ, ∃ (C : Type u) (rc : CommRing C),
    letI := rc
    ∃ (Q : OrientedPrism p C) (η : cechFreeDelta P R n →+* C),
    IsPrismaticEnvelope P (completedFreeDeltaStructure P _) (completedFreeDeltaBase P _)
      (completedFreeDeltaBase_isDeltaHom P _) (cechKernel P R n) (generator_mem_cechKernel P R n) Q η ∧
    IsBoundedPrism Q ∧ Cardinal.mk C ≤ cutoff A R

/-- 概要：多項式代数 R = (A/d)⟨X_T⟩ では envelope が存在する（Ex 3.14 の場合）。
方針：J₀B は、A/d → A の集合論的切断で係数を持ち上げた変数変換により「変数の部分集合 ＋ (d)」になる（a0-design §2.5、紙の検証 2）。
`exists_prismaticEnvelope_of_variables` と `IsPrismaticEnvelope.of_closure`。
規約：T は任意の集合（有限でなくてよい）。
使われ方：Constr 4.18 の定理の範囲。 -/
theorem hasEnvelopes_of_polynomial (hP : IsBoundedPrism P) (T : Type v)
    (hR : Nonempty (R ≃ₐ[A ⧸ P.ideal] prismPolynomialCompletion P T)) :
    HasEnvelopes P R := by
  sorry -- 変数変換 ＋ exists_prismaticEnvelope_of_variables

variable (h : HasEnvelopes P R) (κ : Cardinal.{u}) (hκ : cutoff A R ≤ κ)

/-- 概要：Čech–Alexander の n 項目の対象 C^n ∈ (R/A)_Δ（環の側）。
方針：`HasEnvelopes` から envelope を選び、R → C^n/dC^n は B₀^n → R の持ち上げから。濃度は `HasEnvelopes` の条件（≤ cutoff ≤ κ）。
規約：選択を含む（普遍対象なので同型を除いて一意）。
使われ方：余単体的対象 `cechAlexander`。 -/
def cechAlexanderObj (n : ℕ) : PrismOver P R κ :=
  by
    classical
    let C := (h n).choose
    letI : CommRing C := (h n).choose_spec.choose
    have w := (h n).choose_spec.choose_spec
    let Q := w.choose
    let η := w.choose_spec.choose
    have he := w.choose_spec.choose_spec.1
    have hb := w.choose_spec.choose_spec.2.1
    have hs := w.choose_spec.choose_spec.2.2
    exact {
      B := C
      Q := Q
      bounded := hb
      toHom := { toRingHom := η.comp (completedFreeDeltaBase P _)
                 map_delta := he.isDeltaHom.comp (completedFreeDeltaBase_isDeltaHom P _)
                 ideal_le := he.base_hom }
      sec := by sorry -- 多項式の評価の核が Q.ideal に入るので R から商への射が降下
      sec_comp := by sorry -- 商への射は係数上で構造射に一致
      small := hs.trans hκ }

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
def cechAlexander_isCoproduct (n : ℕ) :
    IsColimit (Cofan.mk (cechAlexanderObj P R h κ hκ n) (fun i : Fin (n+1) =>
      (cechAlexander P R h κ hκ).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))) := by
  sorry -- §5.1：C^n→D は n+1 組の持ち上げ。i 番目への制限はこの標準入射との合成

variable [EssentiallySmall.{u} (PrismOver P R κ)]

/-- 標準頂点を脚とする余積を小さい模型へ移し、site 側で積の Fan として読む。 -/
def smallCechNerveOfCoproducts (X : CosimplicialObject (PrismOver P R κ))
    (hc : ∀ n : ℕ, IsColimit (Cofan.mk (X.obj ⦋n⦌) (fun i : Fin (n+1) =>
      X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)))) :
    CechNerveData (Opposite.op ((equivSmallModel (PrismOver P R κ)).functor.obj (X.obj ⦋0⦌))) where
  obj := (X ⋙ (equivSmallModel (PrismOver P R κ)).functor).op
  proj n i := ((equivSmallModel (PrismOver P R κ)).functor.map
    (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))).op
  isLimit n := by
    have hx := hc n
    sorry -- 同値で標準余積を移し、opposite で同じ脚の積にする
  proj_map := by sorry -- 頂点 i の包含と θ の合成は頂点 θ(i) の包含

/-- Constr 4.18 の C^0 の Čech データ。各次数は指定の C^n。 -/
def cechNerveData : CechNerveData (Opposite.op
    ((equivSmallModel (PrismOver P R κ)).functor.obj (cechAlexanderObj P R h κ hκ 0))) :=
  smallCechNerveOfCoproducts P R κ (cechAlexander P R h κ hκ) (cechAlexander_isCoproduct P R h κ hκ)

theorem cechSmall_weaklyTerminal : IsWeaklyTerminal (Opposite.op
    ((equivSmallModel (PrismOver P R κ)).functor.obj (cechAlexanderObj P R h κ hκ 0))) := by
  sorry -- cechAlexanderObj_weaklyInitial を逆同値の対象に適用し、余単位と opposite で移送

/-- 概要：Constr 4.18 ＋ 脚注 10：O_Δ 上の錐が極限錐 ⇔ C^• への制限（Tot）が極限錐。
方針：S3 の `isLimitCone_iff_restrict_cech` に `cechAlexanderObj_weaklyInitial` と `cechNerveData` を渡す。
規約：O_Δ は D(A) 値前層 `structurePresheafDerived`。層化は経由しない（前層の主張）。
使われ方：`prismaticCohomology_eq_cechAlexanderTot`。 -/
theorem cechAlexander_isLimitCone_iff (c : JoinCone (structurePresheafDerived P R κ)) :
    IsLimitCone c ↔ IsLimitCone (restrictJoinCone c (cechShape (cechNerveData P R h κ hκ))) :=
  isLimitCone_iff_restrict_cech (cechSmall_weaklyTerminal P R h κ hκ)
    (cechNerveData P R h κ hκ) (structurePresheafDerived P R κ) c

/-- 概要：Δ_{R/A} は Tot O_Δ(C^•) に等しい（Constr 4.18 の主張）。
方針：Cor 3.12(d)(e)（O_Δ は層、FlatDescent の `prismaticCohomology_isLimit`）で RΓ = Γ(O_Δ)、`derivedGlobalSections_of_isSheaf`、`cechAlexander_isLimitCone_iff`、`exists_limitCone_of_cech`。
規約：等しさは「同じ頂点をもつ極限錐の存在」（E3 の規約）。
使われ方：A1 の計算を Tot で行う根拠。 -/
theorem prismaticCohomology_eq_cechAlexanderTot (hP : IsBoundedPrism P)
    (hadm : IsAdmissibleCutoff P R κ)
    (hJ : Sheafification (flatTopology P R κ) (derivedInfinityCategory A))
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (derivedInfinityCategory A))
    (t : JoinCone (cechShape (cechNerveData P R h κ hκ) ≫ structurePresheafDerived P R κ))
    (ht : IsLimitCone t) :
    (∃ c : JoinCone (structurePresheafDerived P R κ), IsLimitCone c ∧ c.vertex = t.vertex) ∧
    ∃ e : SSet.Edge (prismaticCohomology P R κ hJ hE) t.vertex, IsInvertibleEdge e.toTruncated := by
  refine ⟨exists_limitCone_of_cech (cechSmall_weaklyTerminal P R h κ hκ)
    (cechNerveData P R h κ hκ) (structurePresheafDerived P R κ) t ht, ?_⟩
  sorry -- prismaticCohomology_isLimit（Cor 3.12(d)(e)）の錐を上の極限錐と比較する

/-- 大きい site の O を制限して RΓ を比較する。HasEnvelopes の各項は両 cutoff に入る。 -/
theorem prismaticCohomology_cutoff_invariant (hP : IsBoundedPrism P)
    (κ' : Cardinal.{u}) [EssentiallySmall.{u} (PrismOver P R κ')]
    (hk : IsAdmissibleCutoff P R κ) (hk' : IsAdmissibleCutoff P R κ') (hle : κ ≤ κ')
    (hJ : Sheafification (flatTopology P R κ) (derivedInfinityCategory A))
    (hJ' : Sheafification (flatTopology P R κ') (derivedInfinityCategory A))
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (derivedInfinityCategory A)) (h : HasEnvelopes P R) :
    let Ores := restrictCutoffStructure P R hle
    let x := derivedGlobalSections (flatTopology P R κ) hJ hE Ores
    Nonempty (FunctorIso Ores (structurePresheafDerived P R κ)) ∧
      (∃ e : SSet.Edge (prismaticCohomology P R κ' hJ' hE) x, IsInvertibleEdge e.toTruncated) ∧
      ∃ e : SSet.Edge (prismaticCohomology P R κ' hJ' hE) (prismaticCohomology P R κ hJ hE),
        IsInvertibleEdge e.toTruncated := by
  sorry -- 小さい模型の同値で Ores を同定。hk.1 と hk'.1 により同じ C^• が入り、
        -- 両側の prismaticCohomology_eq_cechAlexanderTot で同じ Tot と比較する

/-- 概要：Tot を余鎖複体で表す：余単体的 A 加群 [n] ↦ C^n の交代余面複体（非正規化、Mathlib）。
方針：`AlgebraicTopology.alternatingCofaceMapComplex`。
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

/-- Rem 4.19 の模型でも頂点入射が余積の脚になる。 -/
def cechAlexanderAffine_isCoproduct (hP : IsBoundedPrism P) (r : ℕ) (κ : Cardinal.{u})
    (hk : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ) (n : ℕ) :
    let X := cechAlexanderAffine P hP r κ hk
    IsColimit (Cofan.mk (X.obj ⦋n⦌) (fun i : Fin (n+1) =>
      X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))) := by
  sorry -- 差変数の envelope からの写像は n+1 組の独立な座標の持ち上げで決まる

/-- 概要：Rem 4.19 の模型は Constr 4.18 の模型と同じ Δ を計算する（どちらも極限錐）。
方針：両方の C^0 が弱始なので S3 の補題を二度使う。
規約：—
使われ方：計算は小さい模型で、関手性は大きい模型で。 -/
theorem cechAlexanderAffine_computes (hP : IsBoundedPrism P) (r : ℕ) (κ : Cardinal.{u})
    [EssentiallySmall.{u} (PrismOver P (prismPolynomialCompletion P (Fin r)) κ)]
    (hk : IsAdmissibleCutoff P (prismPolynomialCompletion P (Fin r)) κ)
    (hJ : Sheafification (flatTopology P (prismPolynomialCompletion P (Fin r)) κ) (derivedInfinityCategory A))
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (derivedInfinityCategory A)) :
    let R := prismPolynomialCompletion P (Fin r)
    let h := hasEnvelopes_of_polynomial P R hP (Fin r) ⟨AlgEquiv.refl⟩
    let O := structurePresheafDerived P R κ
    let X := cechAlexanderAffine P hP r κ hk.1
    let d := smallCechNerveOfCoproducts P R κ X (cechAlexanderAffine_isCoproduct P hP r κ hk.1)
    let small := cechShape d ≫ O
    ∀ (t : JoinCone (cechShape (cechNerveData P R h κ hk.1) ≫ O)) (s : JoinCone small),
      IsLimitCone t → IsLimitCone s →
        (∃ e : SSet.Edge t.vertex s.vertex, IsInvertibleEdge e.toTruncated) ∧
        ∃ e : SSet.Edge (prismaticCohomology P R κ hJ hE) s.vertex, IsInvertibleEdge e.toTruncated := by
  sorry -- affine 側でも単一 copy が弱始で、差変数の envelope は標準余積。
        -- S3 を両模型に適用すると、それぞれの Tot が同じ O の極限を計算する

/-- 概要：Rem 4.19 の模型は prism の底変換と可換：(A,(d)) → (A′,(d′)) について項ごとの完備底変換が A′ 側の模型（Prop 3.13(2)）。
方針：`prismaticEnvelope_baseChange_of_variables`。
規約：底変換は prism の射に沿う完備テンソル。
使われ方：Lemma 4.20、Constr 6.1、Prop 6.2。 -/
theorem cechAlexanderAffine_baseChange {A' : Type u} [CommRing A'] (P' : OrientedPrism p A')
    (f : OrientedPrism.Hom P P') (hP : IsBoundedPrism P) (hP' : IsBoundedPrism P')
    (r n : ℕ) (κ κ' : Cardinal.{u}) (hk : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ)
    (hk' : cutoff A' (prismPolynomialCompletion P' (Fin r)) ≤ κ') :
    let X := affineEnvelopeTerm P hP r n κ hk
    let Y := affineEnvelopeTerm P' hP' r n κ' hk'
    letI := f.toRingHom.toAlgebra
    letI := X.X.toHom.toRingHom.toAlgebra
    let C' := envelopeBaseChangeRing (A := A) (T := X.X.B) P'
    let l := envelopeBaseLeg (A := A) (T := X.X.B) P'
    let v := envelopeChangeLeg (A := A) (T := X.X.B) P'
    ∃ (Qbc : OrientedPrism p C') (e : (C' : Type u) ≃+* Y.X.B) (g : OrientedPrism.Hom X.X.Q Y.X.Q),
      P'.deltaStructure.IsDeltaHom Qbc.deltaStructure l ∧ X.X.Q.deltaStructure.IsDeltaHom Qbc.deltaStructure v ∧
      Qbc.deltaStructure.IsDeltaHom Y.X.Q.deltaStructure e.toRingHom ∧ Qbc.ideal.map e.toRingHom = Y.X.Q.ideal ∧
      e.toRingHom.comp l = Y.X.toHom.toRingHom ∧ e.toRingHom.comp v = g.toRingHom ∧
      g.comp X.X.toHom = Y.X.toHom.comp f ∧
      ∀ j i, g.toRingHom (X.η (affineVariable P r n j i)) = Y.η (affineVariable P' r n j i) := by
  sorry -- 差変数に対する prismaticEnvelope_baseChange_of_variables と envelope の一意性。
        -- 等式は A′ の係数と各 copy の座標を指定するので単体射による添字の変更とも両立

end SerrePositivity.BhattScholze.Prismatic
