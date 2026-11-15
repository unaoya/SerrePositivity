-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.BaseChange（仮。原典 §4.3 Lemma 4.20・4.22）
-- Tor 振幅と Lemma 4.22（純代数）は SerrePositivity.InfinityCategories.Derived（M13 の隣）へ移す候補。
-- 設計書：formalization-plans/bhatt-scholze/a0-design.md §2.9、単位 A0-4。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.HomologicalAlgebra.CochainCompleteTorAmplitude

public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.BaseChange
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
-- 本ファイルは drafts/A0/{PrismaticSite,CechAlexander}.lean、drafts/DerivedGeneral/{Truncation,CompletionFunctor}.lean
-- （`IsCoconnectiveAt`・`completedBaseChange`）、drafts/Sheaves/GlobalSections.lean を import する。

/-!
# 完備な底変換と Tot、prismatic コホモロジーの底変換（BS 著者版 Lemma 4.22・4.20）

## 概要
Lemma 4.22：有限生成イデアル J = (x₁,…,x_r) を持つ可換環 C と、有限の J 完全 Tor 振幅を持つ C → C′ について、J 完備な底変換
−⊗̂^L_C C′ は D^{≥0}(C) の余単体的対象の Tot（Δ 上の極限）と交換する。
Lemma 4.20：有限の (p,d) 完全 Tor 振幅を持つ有界 prism の射 (A,(d)) → (A′,(d′)) について、Δ_{R/A} ⊗̂^L_A A′ ≃ Δ_{R′/A′}、
Δ̄ も同様。**原典の一般形（p 完全に滑らかな R）ではなく、R = (A/d)⟨X₁,…,X_r⟩（有限変数の p 完備化した多項式代数）の場合**。
R′ = R ⊗̂ A′ は (A′/d′)⟨X₁,…,X_r⟩ で、`prismPolynomialCompletion P' (Fin r)` と書く。

## 方針
Lemma 4.22 は原典の証明：n 骨格では有限極限なので明らか。各 K ∈ D^{≥n}(C) について (K ⊗^L C′) ⊗^L Kos(C′; x) ∈ D^{≥n−c} から、
Kos(C′; x^m) でも同じ c で成り立ち、m の逆極限で K ⊗̂^L C′ ∈ D^{≥n−c}。よって Tot と骨格の Tot の差（fiber）は底変換後も
D^{≥n+1−c} にあり、各次数で一致する。HA の部品は BoundedAboveCompletion・CompletedBaseChange*・Truncation。
Lemma 4.20 は原典の証明：Rem 4.19 の模型の項ごとの完備底変換が A′ 側の模型（`cechAlexanderAffine_baseChange`、Prop 3.13(2)）で、
両側の Δ は Tot で計算され（`cechAlexanderAffine_computes`）、Lemma 4.22 で Tot と底変換を交換する。Δ̄ は mod d で。

## 規約
Tor 振幅は Koszul 版（a0-design §2.9、D4-04）：K ∈ D^{≥m}(C) なら Kos(C′; f(x)) ⊗ (K ⊗^L C′) の H^i は i < m − c で零。原典の商の版と
c が最大 r ずれるが、有限性は同値。完備底変換は drafts/DerivedGeneral/CompletionFunctor の `completedBaseChange`（底変換の後、
x の像で完備化）。余単体的対象は Δ の nerve（宇宙を持ち上げたもの）から D(C) への ∞ 関手、Tot はその極限錐。
Lemma 4.20 の同型は「可逆な辺の存在」（E3 の規約）。**自然な射の指定は含めない**（原典の「the natural map」は Rem 4.19 の模型の
項ごとの射から誘導される射。A1 の Prop 6.2 (b) が η との両立に使うなら、指定した辺の形が要る：A1 の `polynomialChangeEdge`）。

## 使われ方
Construction 6.1(3)（A1 の `crystallineCoverMap_prismaticCohomology`）、Prop 6.2（b̂^*・ĉ^* の比較）、Thm 6.4 の帰着（a1-design §9.1 の 3：
結晶 prism の Δ を Z_p へ）。Lemma 4.22 は A5 の Prop 8.5 でも使う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial

/-! ## Tor 振幅と Lemma 4.22（純代数） -/

namespace SerrePositivity.InfinityCategories.Derived

/-! 完全Tor振幅の仮定は本体の `HasCochainCompleteTorAmplitude` を使う。
全ての非有界入力の半自由分解に対するKoszulホモロジーの下界を検査する。
導来∞圏の頂点への橋渡しは、以下のLemma 4.22の将来の証明の側に残す。 -/

/-- 概要：Lemma 4.22：有限の J 完全 Tor 振幅（J = (x₁,…,x_r)）を持つ f : C → C′ について、J 完備な底変換 −⊗̂^L_C C′ は
D^{≥0}(C) に値をとる余単体的対象の Tot と交換する：Tot の極限錐を `completedBaseChange` で写した錐は D(C′) の極限錐。
方針：原典の証明（§方針）。骨格の Tot（有限極限）は完備底変換（完全関手、`completion_exact`）と交換し、Tot と骨格の Tot の fiber は
D^{≥n+1}、底変換後は Tor 振幅で D^{≥n+1−c}。各次数のコホモロジーで比較する。
規約：原典の一般形（C と f は任意、J は有限生成）。D^{≥0} は `IsCoconnectiveAt C 0`。Δ は `uliftFunctor` で SSet.{u+1} に持ち上げた nerve。
使われ方：`prismaticCohomology_baseChange`、A1 の Prop 6.2、A5 の Prop 8.5。 -/
theorem completedBaseChange_tot_comm {C C' : Type u} [CommRing C] [CommRing C'] [DecidableEq C]
    (f : C →+* C') {r : ℕ} (x : Fin r → C) (c : ℕ) (hf : HasCochainCompleteTorAmplitude f x c)
    (M : (SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategory) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory C)
    (hM : ∀ n : ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategory)) _⦋0⦌,
      IsCoconnectiveAt C 0 (M.app _ n))
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone M) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (completedBaseChange f (Finset.univ.image x)) t) := by
  sorry -- A0-4。骨格の Tot は有限極限で completion_exact、fiber の coconnectivity を Tor 振幅と Koszul 塔の逆極限で

end SerrePositivity.InfinityCategories.Derived

/-! ## Lemma 4.20（多項式代数の場合） -/

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.DerivedCompletion SerrePositivity.InfinityCategories


variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable {A' : Type u} [CommRing A'] (P' : OrientedPrism p A')

open Classical in
/-- 概要：Lemma 4.20（Δ）：有界 prism の射 f : (A,(d)) → (A′,(d′)) が有限の (p,d) 完全 Tor 振幅を持つとき、
R = (A/d)⟨X₁,…,X_r⟩、R′ = (A′/d′)⟨X₁,…,X_r⟩ について Δ_{R/A} ⊗̂^L_A A′ ≃ Δ_{R′/A′}（D(A′) の可逆な辺）。
方針：両側を Rem 4.19 の模型の Tot で表し（`cechAlexanderAffine_computes`）、項ごとの比較 `cechAlexanderAffine_baseChange` と
`completedBaseChange_tot_comm`（各項は離散なので D^{≥0}）。
規約：**原典の一般形（p 完全に滑らかな A/I 代数 R）ではなく、有限変数の多項式代数 R の場合**（E3 に要る適用：Construction 6.1(3)、
Prop 6.2、Thm 6.4 の Z_p への帰着はどれも多項式代数。étale 局所化 Lemma 4.21 は使わない、D24）。完備化は (p,d) の像で。
自然な射の指定は含めない（§規約）。
使われ方：A1 の `crystallineCoverMap_prismaticCohomology`、Prop 6.2、Thm 6.4 の Z_p への帰着（a1-design §9.2。`deRham_iso_polynomial_crystalline` は D68 の改訂で 11-07 に削除）。 -/
theorem prismaticCohomology_baseChange (hP : IsBoundedPrism P) (hP' : IsBoundedPrism P')
    (f : OrientedPrism.Hom P P') (c : ℕ)
    (hf : SerrePositivity.HasCochainCompleteTorAmplitude f.toRingHom ![(p : A), P.generator] c)
    (r : ℕ) (κ κ' : Cardinal.{u})
    [EssentiallySmall.{u} (PrismOver P (prismPolynomialCompletion P (Fin r)) κ)]
    [EssentiallySmall.{u} (PrismOver P' (prismPolynomialCompletion P' (Fin r)) κ')]
    (hk : IsAdmissibleCutoff P (prismPolynomialCompletion P (Fin r)) κ)
    (hk' : IsAdmissibleCutoff P' (prismPolynomialCompletion P' (Fin r)) κ')
    (hJ : _root_.SerrePositivity.InfinityCategories.Sheaves.Sheafification (flatTopology P (prismPolynomialCompletion P (Fin r)) κ) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))
    (hJ' : _root_.SerrePositivity.InfinityCategories.Sheaves.Sheafification (flatTopology P' (prismPolynomialCompletion P' (Fin r)) κ') (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A'))
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))
    (hE' : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A')) :
    ∃ e : SSet.Edge
        ((Derived.completedBaseChange f.toRingHom {(p : A), P.generator}).app _
          (prismaticCohomology P (prismPolynomialCompletion P (Fin r)) κ hJ hE))
        (prismaticCohomology P' (prismPolynomialCompletion P' (Fin r)) κ' hJ' hE'),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated := by
  sorry -- A0-4。cechAlexanderAffine_computes を両側で、cechAlexanderAffine_baseChange の項ごとの同型を Tot に
        -- completedBaseChange_tot_comm で移す（各項は離散で D^{≥0}）

open Classical in
/-- 概要：Lemma 4.20（Δ̄）：同じ仮定で Δ̄_{R/A} ⊗̂^L_A A′ ≃ Δ̄_{R′/A′}。
方針：原典どおり Δ の場合を mod d に落とす（Δ̄ = Δ ⊗^L_A A/d、`hodgeTateCohomology`。A/d ⊗^L_A A′ = A′/d′ は剛性）。
規約：Δ と同じく多項式代数の場合。
使われ方：A1 の HT 比較の底変換（Prop 6.2 (b)）。 -/
theorem hodgeTateCohomology_baseChange (hP : IsBoundedPrism P) (hP' : IsBoundedPrism P')
    (f : OrientedPrism.Hom P P') (c : ℕ)
    (hf : SerrePositivity.HasCochainCompleteTorAmplitude f.toRingHom ![(p : A), P.generator] c)
    (r : ℕ) (κ κ' : Cardinal.{u})
    [EssentiallySmall.{u} (PrismOver P (prismPolynomialCompletion P (Fin r)) κ)]
    [EssentiallySmall.{u} (PrismOver P' (prismPolynomialCompletion P' (Fin r)) κ')]
    (hk : IsAdmissibleCutoff P (prismPolynomialCompletion P (Fin r)) κ)
    (hk' : IsAdmissibleCutoff P' (prismPolynomialCompletion P' (Fin r)) κ')
    (hJ : _root_.SerrePositivity.InfinityCategories.Sheaves.Sheafification (flatTopology P (prismPolynomialCompletion P (Fin r)) κ) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))
    (hJ' : _root_.SerrePositivity.InfinityCategories.Sheaves.Sheafification (flatTopology P' (prismPolynomialCompletion P' (Fin r)) κ') (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A'))
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))
    (hE' : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A')) :
    ∃ e : SSet.Edge
        ((Derived.completedBaseChange f.toRingHom {(p : A), P.generator}).app _
          (hodgeTateCohomology P (prismPolynomialCompletion P (Fin r)) κ hJ hE))
        (hodgeTateCohomology P' (prismPolynomialCompletion P' (Fin r)) κ' hJ' hE'),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated := by
  sorry -- prismaticCohomology_baseChange に A/d との ⊗^L を当て、完備底変換との交換（A/d は完全複体）と剛性 dA′ = (d′)

end SerrePositivity.BhattScholze.Prismatic
