-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.DeRhamComparisonPoly（仮。原典 Thm 6.4 の多項式・mod p の場合）
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md §9、単位 A1-5。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaWitt
-- 本ファイルは drafts/A1/{CrystallineInput,HodgeTateComparison,HodgeTateMap}.lean、drafts/Shared/DeRhamPolynomial.lean、drafts/A2/BaseChangeAndTensor.lean、
-- drafts/A3/LciAndQuasiregular.lean（D4-02 の特殊化だけ）、drafts/A5/RootAdjunction.lean（`polyRootAlgebra`。W9-III-09：WeaklyInitialAndDescent ではなく先行ファイル）を import する。
-- J つき pd 模型（`pdModel`）と `formsCAlg` は drafts/A1/CrystallineInput.lean（W9-III-09）。D68 改訂（11-05 夜）で結晶の黒箱は外した。
-- 11-07（a1-design §10.5）：D69 の大きい模型のため drafts/A0/CechAlexander.lean（`cechAlexander`・`hasEnvelopes_of_polynomial`）と
-- drafts/A2/DerivedPrismaticCohomology.lean（`polyCompletion`・`polyCutoff`・`polyCosimplicialAlgebra`・`prismSiteAlgebras`）も使う。

/-!
# de Rham 比較の多項式・mod p の場合（BS 著者版 Thm 6.4 の特別な場合、A1-5）

## 概要
完全 prism (A,(d))、R = A/d、T = R⟨X_1,…,X_n⟩ について φ_A^*Δ_{T/A} ⊗̂^L_A A/(p,d) ≃ Ω^*_{(T/p)/(R/p)}（D(R/p) の可換代数の自然な同型）。
T_∞ = R⟨X_i^{1/p^∞}⟩ では ≃ T_∞/p。Lemma 8.6（A5-3）の入力。

## 方針
D69（a1-design §9.1、W9-I-15 の訂正後）：完全 prism ← 普遍向き付き prism A_0（Cor 4.12 の底変換）、A_0 上では原典 Thm 6.4 の証明
（ψ : A_0 → W(A_0/d_0)、Thm 5.2 β（`wittSmallBridge_isInvertible`、旧 `wittPdBridge`）、J つき pd 比較 G-A1-17、w_0 に沿う底変換）。D68 改訂（11-05 夜）で
結晶の黒箱はなくなった：Thm 5.2 β は Lemma 5.4（A1/CrystallineInput）と導来 Nakayama で `wittSmallBridge_isInvertible` の中で示す。可換代数構造は各段で保つ。
11-07（a1-design §10.5、D69 は関手の同型のまま）：A_0 上の比較 `deRham_iso_polynomial_universal` は、大きい Čech–Alexander 模型
`bigCechAlexander` と W 上の大きい J つき pd 模型 `wittBigPdModel`（Q^∧ の元すべてを変数にする枠）、C 上の小さい模型 `pdModel C n` の
厳密な自然変換の zigzag（`bigZigzagIso`）で作る。成分の可逆性は小さい模型の結果を枠の取り替え（`pdCechNerveMap_quasiIso`）で移す。

## 規約
Frobenius 捻り φ^*Δ ⊗ A/(p,d) = Δ ⊗_A A/(p, φ^{-1}(d))（完全 prism）。de Rham 複体は Shared/DeRhamPolynomial の cdga を CAlg に。

## 使われ方
A5-3 `rootMap_modP_eq_deRham`。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.BhattScholze.Perfectoidization.Derived
open SerrePositivity.DerivedCompletion
variable (p : ℕ) [Fact p.Prime]

/-- p 完備 CAlg への反射。底の D(k) で完備性を判定する。 -/
def primeCompleteAlg (k : Type u) [CommRing k] :=
  fullSubcomplexOnVertices (CAlg_R k) (fun X => completeAt (p : k) ((cAlgForgetDerived k).app _ X))
instance (k : Type u) [CommRing k] : Quasicategory (primeCompleteAlg p k : SSet) :=
  fullSubcomplexOnVertices_quasicategory _ _
def primeAlgReflection (k : Type u) [CommRing k] :
    Σ L : CAlg_R k ⟶ (primeCompleteAlg p k : SSet), QCatAdjunction L (primeCompleteAlg p k).ι := by
  sorry -- 要確認：G-A2-9 の主元 p に対する CAlg 完備反射
abbrev primeAlgCompletion (k : Type u) [CommRing k] := (primeAlgReflection p k).1 ≫ (primeCompleteAlg p k).ι
abbrev completeChange {k l : Type u} [CommRing k] [CommRing l] (g : k →+* l) :=
  cAlgBaseChange g ≫ primeAlgCompletion p l

abbrev U := universalOrientedPrism.{u} p
abbrev residueU := universalOrientedPrismRing.{u} p ⧸ (U p).ideal
abbrev qU := Ideal.Quotient.mk (U.{u} p).ideal
abbrev WU := WittVector p (residueU.{u} p)

def psiRing : universalOrientedPrismRing.{u} p →+* WU p :=
  WittVector.frobenius.comp ((WittVector.map (qU p)).comp
    (deltaWittGhostRingHom (U p).deltaStructure (by sorry))) -- A₀ は p 正則なので ghostMap は単射

def wittCrystallinePrism : OrientedPrism p (WU.{u} p) := by
  let hp : Function.Injective (fun x : WU.{u} p => (p : WU p)*x) := by sorry -- C=A₀/d₀ は p 正則
  let D := (DeltaStructure.existsUnique_of_mod_p hp WittVector.frobenius
    (by sorry)).exists.choose -- Witt Frobenius は mod p で p 乗
  letI : IsAdicComplete (Ideal.span {(p : WU.{u} p)}) _ := by sorry -- C の p 完備性から Witt 座標で取る
  exact OrientedPrism.crystalline D hp

def psiPrism : OrientedPrism.Hom (U.{u} p) (wittCrystallinePrism p) where
  toRingHom := psiRing p
  map_delta := by sorry -- Witt の標準射と F は Frobenius と可換、標的は p 正則
  ideal_le := by sorry -- can(d₀) の第 0 成分は零、V の像に F を作用させると p の倍数
abbrev wZero : WU.{u} p →+* residueU p := WittVector.constantCoeff
theorem wZero_psi : (wZero.{u} p).comp (psiRing p) = (qU p).comp (U p).deltaStructure.frobeniusLift := by
  sorry -- deltaWittGhostRingHom_frobenius_comp と constantCoeff の合成則

abbrev wittPdIdeal := RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : residueU.{u} p)})).comp (wZero p))
def wittPdStructure : DividedPowers (wittPdIdeal.{u} p) := by
  sorry -- Thm 6.4 の J。V(W(C)) と p の標準 divided powers は共通部分で一致

abbrev universalTwist :=
  polyUnderlying (U.{u} p) (universalOrientedPrism_bounded (p := p)) ≫
    completeChange p ((qU p).comp (U p).deltaStructure.frobeniusLift)

abbrev wittPrismBounded := crystallineBounded p (wittCrystallinePrism.{u} p) rfl
abbrev wittPolynomial (n : ℕ) := polynomialDelta (wittCrystallinePrism.{u} p) (wittPrismBounded p) n

def psiBaseChange (n : ℕ) : VertexIso
    ((polyUnderlying (U p) (universalOrientedPrism_bounded (p := p)) ≫
      completeChange p (psiRing p)).app _ (polyPoint (residueU.{u} p) n)) (wittPolynomial p n) := by
  have hc := prismaticCohomology_baseChange' (U p) (universalOrientedPrism_bounded (p := p)) n
    (wittCrystallinePrism p) (wittPrismBounded p) (psiPrism p)
  sorry -- hc による標準同型。W の (p,p) 完備化を p 完備化と同定し polyDeltaData.obj_eq で移送

/-! ## D69 の厳密に関手的な模型と zigzag（a1-design §10.5、11-07）

C = A₀/d₀（`residueU`）、W = W(C)（`WU`）、J = ker(W → C/p)（`wittPdIdeal`）。Poly(C) の対象 Q = C[X_1..X_n]、Q^∧ = C⟨X⟩（`polyCompletion`）。
以前の J つき pd 模型 `pdModel W n` は持ち上げ W[X] を使い、射 f の持ち上げ f̃ が係数の持ち上げに依存した（C → W に環の切断がない）。
ここでは W 上の模型を**大きい枠**（Q^∧ の元すべてを変数にする、x_q ↦ x_{f(q)}）で作り、C に降りてからは C 上で厳密に関手的な
小さい模型 `pdModel C n` を使う。zigzag の各段は Poly(C) 上の厳密な自然変換で、成分は小さい模型の結果から「表示によらない」補題で移す。 -/

/-- 概要：∞ 圏の係数変換の合成：完備係数変換 g の後に h は h ∘ g の完備係数変換（関手として）。
方針：`cAlgBaseChange` の合成（左随伴の合成、`cAlgRestrictScalars_comp` の随伴）と、完備化は完備化した底変換の後でも不変（反射の冪等性）。
規約：関手 ∞ 圏の同型。
使われ方：`bigZigzagIso` の段 0（q ∘ φ = w₀ ∘ ψ、`wZero_psi`）。 -/
def completeChange_comp {k l m : Type u} [CommRing k] [CommRing l] [CommRing m] (g : k →+* l) (h : l →+* m) :
    FunctorIso (completeChange p g ≫ completeChange p h) (completeChange p (h.comp g)) := by
  sorry -- cAlgBaseChange の合成（随伴の合成）と、primeAlgCompletion の後の底変換の完備化は元の完備底変換

/-- 概要：大きい Čech–Alexander 模型 Q ↦ C_big(Q)^•（A₀ 上、B₀ = A₀{x_{q,i} | q ∈ Q^∧}^∧ の prismatic envelope、BS 著者版 Construction 4.18）を
Poly(C) 上の厳密な関手に。
方針：対象は A0 の `cechAlexander`（R = Q^∧、envelope の存在は `hasEnvelopes_of_polynomial`）を `prismSiteAlgebras` で余単体的 A₀ 代数に。
射 f : Q → Q′ は f̂ : Q^∧ → Q′^∧ による添字の写像 x_{(q,i)} ↦ x_{(f̂ q, i)} の envelope の lift。**envelope は選択して置くが、射は普遍性の
lift で一意**なので map_id・map_comp は厳密に成り立つ（対象の選択は関手性を壊さない）。
規約：cutoff は各 Q の `polyCutoff`（関手の値は A₀ 代数なので cutoff の違いは見えない）。
使われ方：`polyUnderlying_iso_bigCech`、`wittBigBridge`。 -/
def bigCechAlexander : Poly (residueU.{u} p) ⥤ Cosimplicial.CosimplicialAlgebra (universalOrientedPrismRing.{u} p) where
  obj Q := cechAlexander (U p) (polyCompletion (U p) Q.n)
      (hasEnvelopes_of_polynomial (U p) (polyCompletion (U p) Q.n) (universalOrientedPrism_bounded (p := p))
        (Fin Q.n) ⟨AlgEquiv.refl⟩)
      (polyCutoff (U p) Q.n) le_rfl ⋙ prismSiteAlgebras (U p) _ _
  map f := by sorry -- 各項で x_{(q,i)} ↦ x_{(f̂ q, i)}（f̂ は f の p 完備化）の envelope の lift。θ と可換は lift の一意性
  map_id := by sorry -- lift の一意性
  map_comp := by sorry -- lift の一意性

/-- 概要：A₀ 上の Δ_0（A2 の `polyUnderlying`）は大きい Čech–Alexander 模型の Tot_{E∞} と関手 ∞ 圏で同型（BS 著者版 Construction 4.18 ＋ 脚注 10 を
Q について自然に）。
方針：A2 の `polyDeltaData` の docstring どおり、Δ_0 の ∞ 関手としての整合性は大きい模型の厳密な関手性から nerve で作る：
`strictShapeNerve (bigCechAlexander p) ≫ totEInfinityFunctor` を、各頂点での同型（A0 の `prismaticCohomology_eq_cechAlexanderTot` の CAlg 版、
Shared の `derivedGlobalSectionsCAlg_eq_totEInfinity`：site の RΓ の錐を Čech 脈体へ制限、`isLimitCone_iff_restrict_cech`）に沿って
頂点を RΓ に差し替えたものが `polyDeltaData.val`（Joyal の isofibration Fun(K, X) → Fun(sk₀K, X)）。この同型はその構成から出る。
規約：**要相談**：A2 の `PolyDeltaData` にこの同型を欄として持たせるか（今は val・obj_eq・map_eval だけ）。
使われ方：`bigZigzagIso` の段 1。 -/
def polyUnderlying_iso_bigCech :
    FunctorIso (polyUnderlying (U.{u} p) (universalOrientedPrism_bounded (p := p)))
      (Cosimplicial.strictShapeNerve (bigCechAlexander p) ≫ Cosimplicial.totEInfinityFunctor _) := by
  sorry -- A2 の polyDeltaData を大きい模型から頂点の差し替えで作り、その差し替えの同型（要相談：A2 側の欄）

/-- 大きい枠の剰余 Q^∧/p（W 代数の構造は w₀ と C → Q^∧）。 -/
abbrev bigResidue (Q : Poly (residueU.{u} p)) :=
  polyCompletion (U.{u} p) Q.n ⧸ Ideal.span {(p : polyCompletion (U.{u} p) Q.n)}
instance bigResidueAlgebra (Q : Poly (residueU.{u} p)) : Algebra (WU.{u} p) (bigResidue p Q) :=
  ((Ideal.Quotient.mk _).comp ((algebraMap (residueU p) (polyCompletion (U p) Q.n)).comp (wZero p))).toAlgebra

theorem p_mem_wittPdIdeal : (p : WU.{u} p) ∈ wittPdIdeal p := by
  sorry -- w₀(p) = p は C/p で零
theorem wittPdIdeal_le_bigResidue (Q : Poly (residueU.{u} p)) :
    wittPdIdeal p ≤ RingHom.ker (algebraMap (WU.{u} p) (bigResidue p Q)) := by
  sorry -- J = w₀⁻¹(pC) は Q^∧/p で零

/-- 概要：W 上の大きい J つき pd Čech 模型 Q ↦ D_W(Q)^•：枠 W[x_q | q ∈ Q^∧] → Q^∧/p（x_q ↦ q mod p、係数は w₀）の
J つき pd Čech 脈体（`pdCechNerve`、(J, γ) = (`wittPdIdeal`, `wittPdStructure`)）。原典 Thm 6.4 の証明の RΓ_crys((Q/p)/W) の模型を Q について厳密に。
方針：f : Q → Q′ は x_{(q,i)} ↦ x_{(f̂ q, i)}（係数は W のまま、持ち上げの選択がない）の pd 包の lift。関手性は lift の一意性。
規約：添字は `bigCechAlexander` と同じ Q^∧ の台集合（`wittBigBridge` が添字ごとに書ける）。
使われ方：`wittBigBridge`、`wittToSmall`。 -/
def wittBigPdModel : Poly (residueU.{u} p) ⥤ Cosimplicial.CosimplicialAlgebra (WU.{u} p) where
  obj Q := pdCechNerve p (wittPdStructure p) (p_mem_wittPdIdeal p) (wittPdIdeal_le_bigResidue p Q)
    (S := polyCompletion (U p) Q.n) (Ideal.Quotient.mk _)
  map f := by sorry -- 各項で x_{(q,i)} ↦ x_{(f̂ q, i)} の pd 包の lift（R̄ の射 Q^∧/p → Q′^∧/p と両立）
  map_id := by sorry -- lift の一意性
  map_comp := by sorry -- lift の一意性

/-- 概要：D_W(Q)^n は結晶 prism：p ねじれなし・p 完備で、W[x] の δ 構造（δ(x) = 0）が一意に延びる。
方針：p ねじれなしは小さい枠との比較（D_W(Q)^n ≅ D_W^{small,n} ⊗̂ pd 多項式、`pdCechNerveMap_quasiIso` の証明の変数変換）と W(C) の p ねじれなし
（C = A₀/d₀ は p ねじれなし）。δ は BS 著者版 Lemma 2.38 の議論：z ∈ K̄ なら φ(z) = p((p−1)! γ_p(z) + δ(z))、φ(γ_n z) = φ(z)^n/n! が D に入る。
規約：生成元は p。
使われ方：`wittBigBridge`（envelope の普遍性の標的）。 -/
def wittBigCrystalline (Q : Poly (residueU.{u} p)) (n : SimplexCategory) :
    { P : OrientedPrism p (((wittBigPdModel p).obj Q).obj n).right // P.generator = p } := by
  sorry -- p ねじれなし（小さい枠との比較）と Lemma 2.38 型の δ の延長

/-- 概要：結晶の橋（原典 Thm 6.4 の ψ による底変換と Thm 5.2 の比較写像を一つに、大きい模型の上で厳密に自然に）：
余単体的 A₀ 代数の射 C_big(Q)^• → ψ_* D_W(Q)^•、x_{(q,i)} ↦ φ(x_{(q,i)}) = x_{(q,i)}^p、A₀ → W は ψ。
方針：D_W(Q)^n は `wittBigCrystalline` で (A₀,(d₀)) 上の prism（ψ(d₀) ∈ pW）、B₀^n → D_W(Q)^n は自由 δ 環の普遍性の δ 射、
J₀ ↦ pD（z ∈ K̄ なら φ(z) ∈ pD）なので envelope の lift。Q^∧ → D/p（q ↦ x_q^p）で (Q^∧/A₀)_Δ の対象の射。θ・f との可換は lift の一意性。
規約：右辺は `restrictCosimplicial ψ`。原典の比較写像（b ↦ φ(b)）と同じ類を与える（site の対象の射なので Tot の上では選び方によらない、§10.5 の 3）。
使われ方：`bigZigzagIso` の段 2。 -/
def wittBigBridge : bigCechAlexander.{u} p ⟶ wittBigPdModel p ⋙ Cosimplicial.restrictCosimplicial (psiRing p) := by
  sorry -- 各 (Q, n) で envelope の lift（x ↦ φ(x)、基底 ψ）。自然性は lift の一意性

/-- 概要：W → C に沿う先：大きい模型から C 上の小さい模型への厳密な自然変換 D_W(Q)^• → (w₀)_* D_0(Q)^•（D_0 = `pdModel C n`）。
x_{(q,i)} ↦ q^{(i)}（q ∈ Q^∧ = C⟨X⟩ の copy i）、W → C は w₀。
方針：w₀ は pd 射 (J, γ) → (pC + 差, 標準)（`wZero_isDPMorphism`）、枠の射は R̄ = Q^∧/p 上で両立するので pd 包の lift。
Q → Q′ との可換は lift の一意性（右辺の `pdPolynomialFunctor C` は C 係数のまま代入するので厳密）。
規約：§10.5 の 4 の「Ω^*_{Q/C} へつなぐ写像」：第 0 項 D_W(Q)^0 → C⟨X⟩ = Q^∧ が設計の候補（pd 包 → Q、C の (p) の標準 divided powers）
そのもので、de Rham 側は C 上の小さい模型で行う（大きい枠の pd 形式は使わない）。
使われ方：`bigZigzagIso` の段 3。 -/
def wittToSmall : wittBigPdModel.{u} p ⟶
    pdPolynomialFunctor p (residueU p) ⋙ Cosimplicial.restrictCosimplicial (wZero p) := by
  sorry -- 各 (Q, n) で pd 包の lift（x_{(q,i)} ↦ copy i の q、基底 w₀）。自然性は lift の一意性

/-- C の (p) の標準 divided powers（C は p ねじれなし：γ_n(px) = p^n x^n / n!）。 -/
def residuePdStructure : DividedPowers (Ideal.span {(p : residueU.{u} p)}) := by
  sorry -- p^n/n! ∈ pℤ_(p)（n ≥ 1）と C の p ねじれなし
theorem wZero_isDPMorphism : DividedPowers.IsDPMorphism (wittPdStructure.{u} p) (residuePdStructure p) (wZero p) := by
  sorry -- w₀(V x) = 0 と γ_n(V x) = p^{n−1}/n! V(x^n)、w₀(γ_n(p)) = p^n/n!

/-- 概要：完備係数変換と Tot の随伴の転置：厳密な自然変換 α : F ⟶ G ⋙ g_*（F は k 上、G は l 上）から、関手 ∞ 圏の辺
（completeChange g ∘ Tot_k ∘ F ⟹ Tot_l ∘ G）を実際のホモトピーとして。
方針：`strictNatTransHomotopy α` を Tot_k に後合成し、`totEInfinity_restrict`（Tot と係数制限の可換）で Tot_k ∘ g_* ∘ G を g^* ∘ Tot_l ∘ G に移し、
`cAlgBaseChange_restrictScalars_adjunction` の余単位と完備化の反射（G の Tot は p 完備）で転置する（関手 ∞ 圏の随伴は後合成で延びる）。
規約：G の各値の Tot は p 完備（仮定）。
使われ方：`bigZigzagIso` の段 2（g = ψ）・段 3（g = w₀）。 -/
def baseChangeTotHomotopy {k l : Type u} [CommRing k] [CommRing l] (g : k →+* l) {𝒞 : Type u} [SmallCategory 𝒞]
    {F : 𝒞 ⥤ Cosimplicial.CosimplicialAlgebra k} {G : 𝒞 ⥤ Cosimplicial.CosimplicialAlgebra l}
    (α : F ⟶ G ⋙ Cosimplicial.restrictCosimplicial g)
    (hG : ∀ c : 𝒞, completeAt (p : l) ((cAlgForgetDerived l).app _ (Cosimplicial.totEInfinity l (G.obj c)))) :
    SSet.Homotopy (Cosimplicial.strictShapeNerve F ≫ Cosimplicial.totEInfinityFunctor k ≫ completeChange p g)
      (Cosimplicial.strictShapeNerve G ≫ Cosimplicial.totEInfinityFunctor l) := by
  sorry -- 後合成・totEInfinity_restrict・随伴の転置（関手 ∞ 圏へ後合成で延ばした随伴）

/-- 概要：一つの射についての同じ転置：X → g_* Y から辺 completeChange g (Tot_k X) → Tot_l Y。 -/
def baseChangeTotEdge {k l : Type u} [CommRing k] [CommRing l] (g : k →+* l)
    {X : Cosimplicial.CosimplicialAlgebra k} {Y : Cosimplicial.CosimplicialAlgebra l}
    (α : X ⟶ (Cosimplicial.restrictCosimplicial g).obj Y)
    (hY : completeAt (p : l) ((cAlgForgetDerived l).app _ (Cosimplicial.totEInfinity l Y))) :
    SSet.Edge ((completeChange p g).app _ (Cosimplicial.totEInfinity k X)) (Cosimplicial.totEInfinity l Y) := by
  sorry -- totEInfinity_map α、totEInfinity_restrict の成分、随伴の余単位

/-- 概要：`baseChangeTotHomotopy` の頂点での辺は成分の `baseChangeTotEdge`（可逆性が一致）。 -/
theorem baseChangeTotHomotopy_vertex {k l : Type u} [CommRing k] [CommRing l] (g : k →+* l) {𝒞 : Type u} [SmallCategory 𝒞]
    {F : 𝒞 ⥤ Cosimplicial.CosimplicialAlgebra k} {G : 𝒞 ⥤ Cosimplicial.CosimplicialAlgebra l}
    (α : F ⟶ G ⋙ Cosimplicial.restrictCosimplicial g)
    (hG : ∀ c : 𝒞, completeAt (p : l) ((cAlgForgetDerived l).app _ (Cosimplicial.totEInfinity l (G.obj c)))) (c : 𝒞) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge (baseChangeTotHomotopy p g α hG) (ULift.up (nerveVertex c))).toTruncated ↔
      IsInvertibleEdge (baseChangeTotEdge p g (α.app c) (hG c)).toTruncated := by
  sorry -- strictNatTransHomotopy の頂点の辺は nerve.edgeMk (α.app c)、転置は頂点ごとに同じ式

/-- 概要：転置は厳密な射について自然：a : X → X′、b : Y → Y′ と α・α′ が α ≫ g_* b = a ≫ α′ を満たせば、ホモトピー圏で
completeChange g (Tot a) ≫ [α′] = [α] ≫ Tot b。
方針：Tot の関手性と余単位の自然性。
規約：ホモトピー圏の等式（各対象での 2-out-of-3 に使う）。
使われ方：`wittBigBridge_isInvertible`、`wittToSmall_isInvertible`。 -/
theorem baseChangeTotEdge_natural {k l : Type u} [CommRing k] [CommRing l] (g : k →+* l)
    {X X' : Cosimplicial.CosimplicialAlgebra k} {Y Y' : Cosimplicial.CosimplicialAlgebra l}
    (a : X ⟶ X') (b : Y ⟶ Y') (α : X ⟶ (Cosimplicial.restrictCosimplicial g).obj Y)
    (α' : X' ⟶ (Cosimplicial.restrictCosimplicial g).obj Y')
    (h : α ≫ (Cosimplicial.restrictCosimplicial g).map b = a ≫ α')
    (hY : completeAt (p : l) ((cAlgForgetDerived l).app _ (Cosimplicial.totEInfinity l Y)))
    (hY' : completeAt (p : l) ((cAlgForgetDerived l).app _ (Cosimplicial.totEInfinity l Y'))) :
    HomotopyCategory.homMk ((Cosimplicial.totEInfinity_map k a).map (completeChange p g)) ≫
        HomotopyCategory.homMk (baseChangeTotEdge p g α' hY') =
      HomotopyCategory.homMk (baseChangeTotEdge p g α hY) ≫
        HomotopyCategory.homMk (Cosimplicial.totEInfinity_map l b) := by
  sorry -- totEInfinity_map の関手性（h を nerve の 2 単体に）と余単位の自然性

theorem wittBigPdModel_complete (Q : Poly (residueU.{u} p)) :
    completeAt (p : WU.{u} p) ((cAlgForgetDerived _).app _ (Cosimplicial.totEInfinity _ ((wittBigPdModel p).obj Q))) := by
  sorry -- 各項は p 完備（IsCompletedPDEnvelope.complete）、Δ 上の極限は完備性を保つ
theorem pdModel_complete (k : Type u) [CommRing k] (hk : IsAdicComplete (Ideal.span {(p : k)}) k) (r : ℕ) :
    completeAt (p : k) ((cAlgForgetDerived k).app _ (Cosimplicial.totEInfinity k (pdModel p k r))) := by
  sorry -- 各項は p 完備化、極限は完備性を保つ

/-! ### 各対象での可逆性（小さい模型の結果を「表示によらない」で移す、§10.5 の 5） -/

/-- 概要：各対象 Q での小さい Čech–Alexander 模型（Rem 4.19、A2 の `polyCosimplicialAlgebra`）から大きい模型への枠の射（X_j ↦ x_{X_j}）。
選択なしに取れるが Q について自然ではない（各対象での比較だけに使う）。 -/
def cechAlexanderFrame (Q : Poly (residueU.{u} p)) :
    polyCosimplicialAlgebra (U p) (universalOrientedPrism_bounded (p := p)) Q.n ⟶ (bigCechAlexander p).obj Q := by
  sorry -- 各項で X_j^{(i)} ↦ x_{(X_j, i)} の envelope の lift
theorem cechAlexanderFrame_isInvertible (Q : Poly (residueU.{u} p)) :
    IsInvertibleEdge (Cosimplicial.totEInfinity_map _ (cechAlexanderFrame p Q)).toTruncated := by
  sorry -- 両方とも Δ_{Q^∧/A₀} の Čech 脈体（A2 の prismaticCohomologyCAlg_eq_totEInfinity と A0 の
        -- prismaticCohomology_eq_cechAlexanderTot）。枠の射は site の対象の射なので制限の錐と両立し、Tot の上で可逆

/-- 小さい枠 W[X] → 大きい枠（X_j ↦ x_{X_j}）。`pdModel_iso_pdCechNerve` と `pdCechNerveMap`（R̄ の同一視 (W/J)[X] ≅ Q^∧/p を挟む）。 -/
def wittSmallFrame (Q : Poly (residueU.{u} p)) : pdModel p (WU.{u} p) Q.n ⟶ (wittBigPdModel p).obj Q := by
  sorry -- pdModel_iso_pdCechNerve（k = W、J、γ）と pdCechNerveMap（φ(j) = x_{X_j}）、(W/J)[X] ≅ (C/p)[X] ≅ Q^∧/p
theorem wittSmallFrame_isInvertible (Q : Poly (residueU.{u} p)) :
    IsInvertibleEdge (Cosimplicial.totEInfinity_map _ (wittSmallFrame p Q)).toTruncated := by
  sorry -- pdCechNerveMap_quasiIso（どちらの枠も Q^∧/p を覆う、W は p 完備）と totEInfinity_map_isInvertible

/-- 概要：小さい模型での結晶の橋 C_small(n)^• → ψ_* pdModel(W, n)^•（X ↦ X^p、A₀ → W は ψ）。pdModel W n の δ 構造は δ(X) = 0 の延長。 -/
def wittSmallBridge (n : ℕ) :
    polyCosimplicialAlgebra (U.{u} p) (universalOrientedPrism_bounded (p := p)) n ⟶
      (Cosimplicial.restrictCosimplicial (psiRing p)).obj (pdModel p (WU p) n) := by
  sorry -- 各項で envelope の lift（δ 射 X ↦ X^p、基底 ψ）

/-- 概要：小さい模型の原典 Thm 6.4 の核心（ψ に沿う底変換 ＋ Thm 5.2 β）：転置した辺 completeChange ψ (Tot C_small(n)) → Tot pdModel(W, n) は可逆。
方針：`psiBaseChange`（Cor 4.12）と A0 の `cechAlexanderAffine_baseChange` で左辺を W 上の Čech–Alexander 模型 C_W(T′)^• の Tot に、
W 上の Thm 5.2 β：mod p は Lemma 5.4（`frobeniusTwist_cech_quasiIso_infinite`、k = W/p）と G-A1-16 の mod p 版、持ち上げは両辺 p 完備なので
導来 Nakayama（G-A1-4）。旧 `wittPdBridge`（VertexIso の存在）をこの辺の可逆性に置き換えた。
規約：—
使われ方：`wittBigBridge_isInvertible`。 -/
theorem wittSmallBridge_isInvertible (n : ℕ) :
    IsInvertibleEdge (baseChangeTotEdge p (psiRing p) (wittSmallBridge.{u} p n)
      (pdModel_complete p (WU p) (by sorry) n)).toTruncated := by
  sorry -- psiBaseChange・cechAlexanderAffine_baseChange・Lemma 5.4（無限変数、k = W/p）・G-A1-16・導来 Nakayama
        -- （W の p 完備性の sorry は wittCrystallinePrism と同じ根拠）

theorem wittBridge_frame_comm (Q : Poly (residueU.{u} p)) :
    wittSmallBridge p Q.n ≫ (Cosimplicial.restrictCosimplicial (psiRing p)).map (wittSmallFrame p Q) =
      cechAlexanderFrame p Q ≫ (wittBigBridge p).app Q := by
  sorry -- envelope の lift の一意性：両辺とも X_j^{(i)} ↦ φ(x_{(X_j,i)}) = x_{(X_j,i)}^p の δ 射

/-- 概要：段 2 の成分は可逆。
方針：`baseChangeTotEdge_natural`（`wittBridge_frame_comm`）の四角形で、`cechAlexanderFrame_isInvertible`（の完備係数変換）・
`wittSmallBridge_isInvertible`・`wittSmallFrame_isInvertible` から 2-out-of-3。 -/
theorem wittBigBridge_isInvertible (Q : Poly (residueU.{u} p)) :
    IsInvertibleEdge (baseChangeTotEdge p (psiRing p) ((wittBigBridge p).app Q) (wittBigPdModel_complete p Q)).toTruncated := by
  sorry -- 四角形と 2-out-of-3

/-- 小さい模型の係数変換 pdModel(W, n) → (w₀)_* pdModel(C, n)（係数 w₀、X ↦ X）。 -/
def pdModelBaseChange (n : ℕ) :
    pdModel p (WU.{u} p) n ⟶ (Cosimplicial.restrictCosimplicial (wZero p)).obj (pdModel p (residueU p) n) := by
  sorry -- 各項で pdRaw の係数変換を完備化
/-- 概要：小さい模型の係数変換は Tot で可逆（完備底変換と Tot が可換）。
方針：W 上と C 上の de Rham 比較（`pdDeRhamFunctorIso` の成分）は係数変換と厳密に両立し、Ω̂^•_{W⟨X⟩} ⊗̂_W C ≅ Ω̂^•_{C⟨X⟩}（各次数有限自由、有界）。 -/
theorem pdModelBaseChange_isInvertible (n : ℕ) :
    IsInvertibleEdge (baseChangeTotEdge p (wZero p) (pdModelBaseChange.{u} p n)
      (pdModel_complete p (residueU p) (by sorry) n)).toTruncated := by
  sorry -- de Rham の span（行 0・列 0 の射影）は係数変換と可換、有界で有限自由な Ω の完備底変換
        -- （C の p 完備性の sorry は C = A₀/d₀ が有界 prism の剰余であることから）

theorem wittToSmall_frame (Q : Poly (residueU.{u} p)) :
    wittSmallFrame p Q ≫ (wittToSmall p).app Q = pdModelBaseChange p Q.n := by
  sorry -- pd 包の lift の一意性：X_j ↦ x_{X_j} ↦ X_j

/-- 概要：段 3 の成分は可逆。
方針：`baseChangeTotEdge_natural`（a = `wittSmallFrame`、b = 𝟙、`wittToSmall_frame`）で `pdModelBaseChange_isInvertible` と
`wittSmallFrame_isInvertible` から 2-out-of-3。 -/
theorem wittToSmall_isInvertible (Q : Poly (residueU.{u} p)) :
    IsInvertibleEdge (baseChangeTotEdge p (wZero p) ((wittToSmall p).app Q)
      (pdModel_complete p (residueU p) (by sorry) Q.n)).toTruncated := by
  sorry -- 四角形と 2-out-of-3

/-! ### 組み立て -/

/-- 概要：D69 の比較同型を関手 ∞ 圏 Fun(N(Poly(C)), CAlg_C) の同型として：φ_0^*Δ_{(−)/A₀} ⊗̂ C ≅ Ω̂^•_{(−)/C}（原典 Thm 6.4 の証明を A₀ で）。
方針：段 0〜4 の合成（a1-design §10.5）：
0. q ∘ φ = w₀ ∘ ψ（`wZero_psi`）と `completeChange_comp`。
1. `polyUnderlying_iso_bigCech`（Δ_0 ≅ Tot C_big）を後合成。
2. `wittBigBridge` の転置 `baseChangeTotHomotopy`（ψ）、成分は `wittBigBridge_isInvertible`、`functorIsoOfPointwiseInvertibleHomotopy`。w₀ を後合成。
3. `wittToSmall` の転置（w₀）、成分は `wittToSmall_isInvertible`。
4. `pdDeRhamFunctorIso`（k = C）。
規約：∞ 関手の合成の結合は `functorIsoOfEq` で調整。
使われ方：`wittComposite`、`deRham_iso_polynomial_universal`。 -/
def bigZigzagIso : FunctorIso (universalTwist.{u} p) (formsCAlg p (residueU p)) := by
  let hU := universalOrientedPrism_bounded (p := p)
  let Δ0 := polyUnderlying (U.{u} p) hU
  let cψ := completeChange p (psiRing.{u} p)
  let cw := completeChange p (wZero.{u} p)
  let SA := Cosimplicial.strictShapeNerve (bigCechAlexander.{u} p)
  let SD := Cosimplicial.strictShapeNerve (wittBigPdModel.{u} p)
  let S0 := Cosimplicial.strictShapeNerve (pdPolynomialFunctor p (residueU.{u} p))
  let TA := Cosimplicial.totEInfinityFunctor (universalOrientedPrismRing.{u} p)
  let TW := Cosimplicial.totEInfinityFunctor (WU.{u} p)
  let TC := Cosimplicial.totEInfinityFunctor (residueU.{u} p)
  -- 段 0
  let e0 : FunctorIso (universalTwist p) (Δ0 ≫ cψ ≫ cw) :=
    functorIsoOfEq ((completeChange_comp p (psiRing p) (wZero p)).symm.precomp Δ0) (by rw [wZero_psi]) rfl
  -- 段 1
  let e1 : FunctorIso (Δ0 ≫ cψ ≫ cw) (SA ≫ TA ≫ cψ ≫ cw) :=
    functorIsoOfEq ((polyUnderlying_iso_bigCech p).postcomp (cψ ≫ cw)) rfl (by simp only [Category.assoc])
  -- 段 2
  let e2 : FunctorIso (SA ≫ TA ≫ cψ ≫ cw) (SD ≫ TW ≫ cw) :=
    functorIsoOfEq ((functorIsoOfPointwiseInvertibleHomotopy
        (baseChangeTotHomotopy p (psiRing p) (wittBigBridge p) (wittBigPdModel_complete p)) (by
          sorry)).postcomp cw) -- 頂点 ULift.up (nerveVertex Q) で baseChangeTotHomotopy_vertex と wittBigBridge_isInvertible
      (by simp only [Category.assoc]) (by simp only [Category.assoc])
  -- 段 3
  let e3 : FunctorIso (SD ≫ TW ≫ cw) (S0 ≫ TC) :=
    functorIsoOfEq (functorIsoOfPointwiseInvertibleHomotopy
        (baseChangeTotHomotopy p (wZero p) (wittToSmall p) (fun Q => pdModel_complete p (residueU p) (by sorry) Q.n)) (by
          sorry)) -- 頂点で baseChangeTotHomotopy_vertex と wittToSmall_isInvertible。C の p 完備性は上と同じ
      (by simp only [Category.assoc]) rfl
  -- 段 4
  exact e0 ≪≫ e1 ≪≫ e2 ≪≫ e3 ≪≫ pdDeRhamFunctorIso p (residueU p)

/-- 概要：D69 の比較同型の各 n での成分（11-07、§10.5 の決定）：**大きい模型を通る zigzag の成分として定義し直した**。
方針：`bigZigzagIso` の `FunctorIso.app`。以前の定義（小さい模型の四本の脚 `WittComparisonLegs` の合成）は持ち上げの選択に依存し
関手にならないので外した。小さい模型の結果は各対象での可逆性（`wittSmallBridge_isInvertible` など）に使う。
規約：—
使われ方：`deRham_iso_polynomial_universal` の型の条件。 -/
def wittComposite (n : ℕ) := (bigZigzagIso.{u} p).app (polyPoint _ n)

/-- 概要：A_0 上の比較同型（原典 Thm 6.4 の証明を A_0 で、D69）。成分は `wittComposite`。11-07：関手としての同型のまま（D69 の決定）。
方針：大きい模型の厳密な zigzag `bigZigzagIso`（a1-design §10.5）。成分の条件は `wittComposite` の定義から。
規約：`FunctorIso` は Fun(N(Poly), CAlg) のホモトピー圏の同型。高次の整合性は厳密な関手・自然変換の nerve から来る（§10.4 の (i)〜(iii)）。
使われ方：`transferWittComparison`。 -/
def deRham_iso_polynomial_universal :
    { e : FunctorIso (universalTwist.{u} p) (formsCAlg p (residueU p)) //
      ∀ n, e.app (polyPoint _ n) = wittComposite p n } :=
  ⟨bigZigzagIso p, fun _ => rfl⟩

variable {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)
abbrev modOrientation : A →+* modPrime p (A ⧸ P.ideal) :=
  (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ P.ideal)})).comp (Ideal.Quotient.mk P.ideal)
abbrev twistedReduction := (modOrientation p P).comp P.deltaStructure.frobeniusLift
abbrev reducedPolyDelta := polyUnderlying P hP ≫ completeChange p (twistedReduction p P)
abbrev reducedPolyForms := changePolyNerve (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ P.ideal)})) ≫
  formsCAlg p (modPrime p (A ⧸ P.ideal))

/-- A₀ で既に構成した射を d₀↦d に沿って移す。 -/
abbrev residueToModP := (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ P.ideal)})).comp (orientationMap P).quotientMap

def universalDeltaChange (n : ℕ) : VertexIso ((reducedPolyDelta p P hP).app _ (polyPoint _ n))
    ((completeChange p (residueToModP p P)).app _ ((universalTwist p).app _ (polyPoint _ n))) := by
  sorry -- 分類射による polynomialChangeEdge は Cor 4.12 で可逆。
        -- δ 射と φ の両立、完備底変換の結合則でその逆を取る
def universalFormsChange (n : ℕ) : VertexIso
    ((completeChange p (residueToModP p P)).app _ (formsVertex p (residueU p) n))
    ((reducedPolyForms p P).app _ (polyPoint _ n)) := by
  sorry -- 有限自由な連続形式の底変換。座標とその微分を同じ座標へ送る

def transferWittComparison (hperf : P.deltaStructure.IsPerfect) :
    { e : FunctorIso (reducedPolyDelta p P hP) (reducedPolyForms p P) // ∀ n : ℕ,
      e.app (polyPoint _ n) = universalDeltaChange p P hP n ≪≫
        ((deRham_iso_polynomial_universal p).val.app (polyPoint _ n)).map (completeChange p (residueToModP p P)) ≪≫
        universalFormsChange p P n } := by
  sorry -- 普遍例で構成した比較を分類射に沿って移す。係数・多項式の持ち上げに関する
        -- J つき比較の自然性により各成分が多項式射と可換

def deRham_iso_polynomial_modP (hperf : P.deltaStructure.IsPerfect) :
    FunctorIso (reducedPolyDelta p P hP) (reducedPolyForms p P) :=
  (transferWittComparison p P hP hperf).val

abbrev rootSource (C : Type u) [CommRing C] := formsVertex p C 1
abbrev rootTargetAlgebra (n : ℕ) : A_R (modPrime p (A ⧸ P.ideal)) := by
  let R := A ⧸ P.ideal
  let S := polyRootAlgebra p R n
  exact Under.mk (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(p : S)}) (algebraMap R S) (by
    sorry))) -- p の像は p

abbrev rootStrictTarget (n : ℕ) :=
  (commAlgCatEquivUnder (CommRingCat.of (modPrime p (A ⧸ P.ideal)))).inverse.obj (rootTargetAlgebra p P n)

def rootDegreeZeroMap (n : ℕ) :
    MvPolynomial (Fin n) (modPrime p (A ⧸ P.ideal)) →ₐ[modPrime p (A ⧸ P.ideal)] (rootStrictTarget p P n) :=
  let C := modPrime p (A ⧸ P.ideal)
  MvPolynomial.aeval (R := C) (fun j : Fin n =>
    Ideal.Quotient.mk (Ideal.span {(p : polyRootAlgebra p (A ⧸ P.ideal) n)})
      (polyRootAlgebraVar p (A ⧸ P.ideal) n j 0))

abbrev singleRootTarget (n : ℕ) :=
  let C := modPrime p (A ⧸ P.ideal)
  (CochainComplex.singleFunctor (ModuleCat C) 0).mapCommMon.obj
    ((moduleCommMonoidFunctor C).obj (rootStrictTarget p P n))

def polynomialZeroForm (C : Type u) [CommRing C] (n : ℕ) :
    MvPolynomial (Fin n) C →+ (formComplex p C n).X 0 := by
  sorry -- Ω⁰=多項式環を ULift の変数に rename、completedFormsUnit と extendXIso で次数零へ
def singleTargetZeroIso (n : ℕ) :
    (singleRootTarget p P n).X.X 0 ≃+ (rootStrictTarget p P n) := by
  sorry -- HomologicalComplex.singleObjXSelf の底の加法同型

def cdgaAugmentation (n : ℕ) :
    let C := modPrime p (A ⧸ P.ideal)
    { f : formsCDGA p C n ⟶ singleRootTarget p P n //
      ∀ a : MvPolynomial (Fin n) C, singleTargetZeroIso p P n
        (f.hom.hom.f 0 (polynomialZeroForm p C n a)) = rootDegreeZeroMap p P n a } := by
  sorry -- 次数零は rootDegreeZeroMap（p=0）、正次数では標的が零。
        -- 単位・外積・微分に両立する CommMon の射を作る

def rootFormsAugmentation (n : ℕ) :
    SSet.Edge (formsVertex p (modPrime p (A ⧸ P.ideal)) n)
      ((algebraEmbedding _).app _ (nerveVertex (rootTargetAlgebra p P n))) := by
  let C := modPrime p (A ⧸ P.ideal)
  let F := commutativeAlgebraFunctor C ⋙ Operad.restrictAlgebra (augmentation C)
  let e := (nerve.edgeMk (F.map (cdgaAugmentation p P n).val)).map (algebraCAlgSource C)
  exact e -- 同じ cofibrant 置換により両端は formsVertex と離散代数の像

def rootArrow (n : ℕ) : ofAlgebra (A ⧸ P.ideal) (polyAlgebra p (A ⧸ P.ideal) n) ⟶
    ofAlgebra (A ⧸ P.ideal) (polyRootAlgebra p (A ⧸ P.ideal) n) :=
  Under.homMk (CommRingCat.ofHom (polyAlgebraToRoot p _ n)) (by sorry) -- 両端の係数を保つ
abbrev rootDeltaEdge (n : ℕ) := (nerve.edgeMk (rootArrow p P n)).map
  (derivedPrismaticCohomologyDiscrete P hP ≫ prismCompleteInclusion P ≫ completeChange p (twistedReduction p P))

/-- 完備離散入力 T での値を polyUnderlying の多項式頂点に移送する。 -/
def completedPolynomialRecovery (n : ℕ) :
    VertexIso ((derivedPrismaticCohomologyDiscrete P hP ≫ prismCompleteInclusion P ≫
      completeChange p (twistedReduction p P)).app _ (nerveVertex (ofAlgebra _ (polyAlgebra p (A ⧸ P.ideal) n))))
      ((reducedPolyDelta p P hP).app _ (polyPoint _ n)) := by
  sorry -- A2 の polyRecovery、離散多項式の p 完備化は有界ねじれで次数零、D32

theorem deRham_iso_rootAlgebra_modP (hperf : P.deltaStructure.IsPerfect) (n : ℕ) :
    let g := rootFormsAugmentation p P n
    let e := completedPolynomialRecovery p P hP n ≪≫ (deRham_iso_polynomial_modP p P hP hperf).app (polyPoint _ n)
    ∃ e∞ : VertexIso ((derivedPrismaticCohomologyDiscrete P hP ≫ prismCompleteInclusion P ≫
        completeChange p (twistedReduction p P)).app _ (nerveVertex (ofAlgebra _ (polyRootAlgebra p (A ⧸ P.ideal) n))))
        ((algebraEmbedding _).app _ (nerveVertex (rootTargetAlgebra p P n))),
      HomotopyCategory.homMk (rootDeltaEdge p P hP n) ≫ e∞.hom = e.hom ≫ HomotopyCategory.homMk g := by
  sorry -- X_j↦X_j^p の列の完備 filtered 余極限。mod p で正次数の形式の遷移は零、
        -- 次数零は T∞/p。最初の余極限脚で可換式を得る

/-! A3 は A2 の底変換を使うため、普遍例への特殊化は A1 の最終ファイルに置く。 -/
theorem prismaticCohomology_lci_universal {r : ℕ} (f : Fin r → A)
    (hf : IsKoszulRegularModGenerator P f) (hb : BoundedPTorsion p (lciQuotient P f)) :
    let R := lciQuotient P f
    let h := lci_isDiscretePrismatic P hP f hf hb
    ∃ t : InitialDelta P hP R h, IsLciEnvelope P f (discretePrism P hP R h t.D t.base) (discreteBase P hP R) := by
  obtain ⟨g, hg, _⟩ := universalOrientedPrism_hom P
  exact prismaticCohomology_lci_eq_envelope P hP f (U p) (universalOrientedPrism_bounded (p := p)) g hg hf hb

end SerrePositivity.BhattScholze.Prismatic
