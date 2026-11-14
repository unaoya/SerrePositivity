-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.CechAlexander（仮。原典 §4.3 Constr 4.17・4.18、Rem 4.19）
-- 設計書：formalization-plans/bhatt-scholze/a0-design.md §2.8、単位 A0-2。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.AffineCechPrismBaseChange
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.AffineCechSiteNerve
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderAssembly
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderSmall
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Complexes.CechAlexanderComplex
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Complexes.CechAlexanderFreeDelta
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.CechAlexanderEnvelopeData

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.AffinePolynomial

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

/-! ## envelope の選択（Prop 3.13 の適用） -/

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

/-! ## 性質（多項式代数の R について） -/

variable [EssentiallySmall.{u} (PrismOver P R κ)]

/-- 概要：Constr 4.18 ＋ 脚注 10：O_Δ 上の錐が極限錐 ⇔ C^• への制限（Tot）が極限錐。
方針：S3 の `isLimitCone_iff_restrict_cech` に `cechAlexanderObj_weaklyInitial` と `cechNerveData` を渡す。
規約：O_Δ は D(A) 値前層 `structurePresheafDerived`。層化は経由しない（前層の主張）。
使われ方：`prismaticCohomology_eq_cechAlexanderTot`。 -/
theorem cechAlexander_isLimitCone_iff (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (structurePresheafDerived P R κ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c (_root_.SerrePositivity.InfinityCategories.Sheaves.cechShape (cechNerveData P R κ h hκ))) :=
  _root_.SerrePositivity.InfinityCategories.Sheaves.isLimitCone_iff_restrict_cech (cechSmall_weaklyTerminal P R κ h hκ)
    (cechNerveData P R κ h hκ) (structurePresheafDerived P R κ) c

/-- 概要：Δ_{R/A} は Tot O_Δ(C^•) に等しい（Constr 4.18 の主張）。
方針：Cor 3.12(d)(e)（O_Δ は層、FlatDescent の `prismaticCohomology_isLimit`）で RΓ = Γ(O_Δ)、`derivedGlobalSections_of_isSheaf`、`cechAlexander_isLimitCone_iff`、`exists_limitCone_of_cech`。
規約：等しさは「同じ頂点をもつ極限錐の存在」（E3 の規約）。
使われ方：A1 の計算を Tot で行う根拠。 -/
theorem prismaticCohomology_eq_cechAlexanderTot (hP : IsBoundedPrism P)
    (hadm : IsAdmissibleCutoff P R κ)
    (hJ : _root_.SerrePositivity.InfinityCategories.Sheaves.Sheafification (flatTopology P R κ) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Sheaves.cechShape (cechNerveData P R κ h hκ) ≫ structurePresheafDerived P R κ))
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone t) :
    (∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (structurePresheafDerived P R κ), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ c.vertex = t.vertex) ∧
    ∃ e : SSet.Edge (prismaticCohomology P R κ hJ hE) t.vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Sheaves.exists_limitCone_of_cech (cechSmall_weaklyTerminal P R κ h hκ)
    (cechNerveData P R κ h hκ) (structurePresheafDerived P R κ) t ht, ?_⟩
  sorry -- prismaticCohomology_isLimit（Cor 3.12(d)(e)）の錐を上の極限錐と比較する

/-- 大きい site の O を制限して RΓ を比較する。HasEnvelopes の各項は両 cutoff に入る。 -/
theorem prismaticCohomology_cutoff_invariant (hP : IsBoundedPrism P)
    (κ' : Cardinal.{u}) [EssentiallySmall.{u} (PrismOver P R κ')]
    (hk : IsAdmissibleCutoff P R κ) (hk' : IsAdmissibleCutoff P R κ') (hle : κ ≤ κ')
    (hJ : _root_.SerrePositivity.InfinityCategories.Sheaves.Sheafification (flatTopology P R κ) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))
    (hJ' : _root_.SerrePositivity.InfinityCategories.Sheaves.Sheafification (flatTopology P R κ') (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)) (h : HasEnvelopes P R) :
    let Ores := restrictCutoffStructure P R hle
    let x := _root_.SerrePositivity.InfinityCategories.Sheaves.derivedGlobalSections (flatTopology P R κ) hJ hE Ores
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso Ores (structurePresheafDerived P R κ)) ∧
      (∃ e : SSet.Edge (prismaticCohomology P R κ' hJ' hE) x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated) ∧
      ∃ e : SSet.Edge (prismaticCohomology P R κ' hJ' hE) (prismaticCohomology P R κ hJ hE),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated := by
  sorry -- 小さい模型の同値で Ores を同定。hk.1 と hk'.1 により同じ C^• が入り、
        -- 両側の prismaticCohomology_eq_cechAlexanderTot で同じ Tot と比較する

/-! ## Rem 4.19：affine 空間の小さい模型 -/

/-- 概要：Rem 4.19 の模型は Constr 4.18 の模型と同じ Δ を計算する（どちらも極限錐）。
方針：両方の C^0 が弱始なので S3 の補題を二度使う。
規約：—
使われ方：計算は小さい模型で、関手性は大きい模型で。 -/
theorem cechAlexanderAffine_computes (hP : IsBoundedPrism P) (r : ℕ) (κ : Cardinal.{u})
    [EssentiallySmall.{u} (PrismOver P (prismPolynomialCompletion P (Fin r)) κ)]
    (hk : IsAdmissibleCutoff P (prismPolynomialCompletion P (Fin r)) κ)
    (hJ : _root_.SerrePositivity.InfinityCategories.Sheaves.Sheafification (flatTopology P (prismPolynomialCompletion P (Fin r)) κ) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)) :
    let R := prismPolynomialCompletion P (Fin r)
    let h := hasEnvelopes_of_polynomial P R hP (Fin r) ⟨AlgEquiv.refl⟩
    let O := structurePresheafDerived P R κ
    let X := cechAlexanderAffine P hP r κ hk.1
    let d := smallCechNerveOfCoproducts P R κ X (cechAlexanderAffine_isCoproduct P hP r κ hk.1)
    let small := _root_.SerrePositivity.InfinityCategories.Sheaves.cechShape d ≫ O
    ∀ (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Sheaves.cechShape (cechNerveData P R κ h hk.1) ≫ O)) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone small),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone t → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone s →
        (∃ e : SSet.Edge t.vertex s.vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated) ∧
        ∃ e : SSet.Edge (prismaticCohomology P R κ hJ hE) s.vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated := by
  sorry -- affine 側でも単一 copy が弱始で、差変数の envelope は標準余積。
        -- S3 を両模型に適用すると、それぞれの Tot が同じ O の極限を計算する

end SerrePositivity.BhattScholze.Prismatic
