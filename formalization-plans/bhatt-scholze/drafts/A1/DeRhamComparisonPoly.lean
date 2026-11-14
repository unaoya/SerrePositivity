-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.DeRhamComparisonPoly（仮。原典 Thm 6.4 の多項式・mod p の場合）
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md §9、単位 A1-5。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.UniversalWittComparison
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.UniversalWittComparison
import all SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.BigCechAffineEnvelope
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineForms
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.BigPDModel
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDModelBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittBigBridge
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittBigCrystalline
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittCrystallinePrism
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDBase
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittSmallFrame
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittToSmall
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittToSmallFrame

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaWitt
-- 本ファイルは drafts/A1/{CrystallineInput,HodgeTateComparison,HodgeTateMap}.lean、drafts/Shared/DeRhamPolynomial.lean、drafts/A2/BaseChangeAndTensor.lean、
-- drafts/A3/LciAndQuasiregular.lean（D4-02 の特殊化だけ）、drafts/A5/RootAdjunction.lean（`polyRootAlgebra`。W9-III-09：WeaklyInitialAndDescent ではなく先行ファイル）を import する。
-- J つき pd 模型（`pdModel`）は A1/CrystallineInput、`theoryFormsCAlg` は A1/CrystallineSite（W9-III-09）。D68 改訂（11-05 夜）で結晶の黒箱は外した。
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
結晶の黒箱はなくなった：Thm 5.2 は A1/CrystallineSite の (c)（`crystallineComparison_polynomial`、比較写像は原典の η）を (W, J) で使い、
`wittSmallBridge_isInvertible` の中で X ↦ X^p の形（`frobeniusPdBridge_tot`）に読む。可換代数構造は各段で保つ。
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

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories SerrePositivity.EInfinity
open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.BhattScholze.Perfectoidization.Derived
open SerrePositivity.DerivedCompletion
variable (p : ℕ) [Fact p.Prime]

/-- p 完備 CAlg への反射。底の D(k) で完備性を判定する。 -/
def primeCompleteAlg (k : Type u) [CommRing k] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (E.CAlg k) (fun X => completeAt (p : k) ((E.forget k).app _ X))
instance (k : Type u) [CommRing k] : Quasicategory (primeCompleteAlg (E := E) p k : SSet) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _
def primeAlgReflection (k : Type u) [CommRing k] :
    Σ L : E.CAlg k ⟶ (primeCompleteAlg (E := E) p k : SSet), _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L (primeCompleteAlg (E := E) p k).ι := by
  sorry -- 要確認：G-A2-9 の主元 p に対する CAlg 完備反射
abbrev primeAlgCompletion (k : Type u) [CommRing k] := (primeAlgReflection (E := E) p k).1 ≫ (primeCompleteAlg (E := E) p k).ι
abbrev completeChange {k l : Type u} [CommRing k] [CommRing l] (g : k →+* l) :=
  cAlgBaseChange (E := E) g ≫ primeAlgCompletion (E := E) p l

abbrev U := universalOrientedPrism.{u} p
abbrev residueU := universalOrientedPrismRing.{u} p ⧸ (U p).ideal
abbrev qU := Ideal.Quotient.mk (U.{u} p).ideal
abbrev WU := WittVector p (residueU.{u} p)

local instance : IsAdicComplete (Ideal.span {(p : residueU.{u} p)}) (residueU.{u} p) := (universalOrientedResidue_complete.{u} p)
local instance : Algebra (WU.{u} p) (residueU.{u} p) := (wZero p (residueU p)).toAlgebra

/-- p 完備な普遍剰余環では p と互いに素な整数は単元。 -/
theorem universalResidue_natCast_unit (m : ℕ) (hm : ¬p ∣ m) :
    IsUnit (m : residueU.{u} p) := by
  have hcop := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hm
  have he : IsCoprime (p : residueU.{u} p) (m : residueU.{u} p) := by
    simpa only [map_natCast] using hcop.isCoprime.map (Int.castRingHom (residueU.{u} p))
  obtain ⟨a, b, h⟩ := he
  have hmem : b * (m : residueU.{u} p) - 1 ∈ Ideal.jacobson (⊥ : Ideal (residueU.{u} p)) := by
    have h' : b * (m : residueU.{u} p) - 1 = -(a * (p : residueU.{u} p)) := by rw [← h]; ring
    rw [h']
    apply (Ideal.jacobson (⊥ : Ideal (residueU.{u} p))).neg_mem
    apply Ideal.mul_mem_left
    exact IsAdicComplete.le_jacobson_bot (Ideal.span {(p : residueU.{u} p)})
      (Ideal.mem_span_singleton_self _)
  exact isUnit_of_mul_isUnit_right (Ideal.isUnit_of_sub_one_mem_jacobson_bot _ hmem)

/-- 普遍 prism の既存の正則性を乗法の単射性として読む。 -/
theorem universalPrime_mul_injective :
    Function.Injective (fun x : universalOrientedPrismRing.{u} p => (p : universalOrientedPrismRing.{u} p) * x) := by
  simpa only [IsSMulRegular, smul_eq_mul] using (universalOrientedPrism_regular.{u} p).1

/-- BS 著者版 Theorem 6.4 の普遍基底に本体の大きいpd模型を特殊化する。 -/
abbrev universalWittPdFunctor := wittBigPdModel (U.{u} p) (universalOrientedPrism_mod_generator_p_regular.{u} p) (universalResidue_natCast_unit.{u} p)

/-- BS 著者版 Theorem 6.4 の有限枠の本体の比較を普遍基底へ特殊化する。 -/
abbrev universalWittSmallFrame (Q : Poly (residueU.{u} p)) :=
  wittSmallFrame (U.{u} p) (universalOrientedPrism_mod_generator_p_regular.{u} p) (universalResidue_natCast_unit.{u} p) Q (universalOrientedResidue_complete.{u} p)

/-- BS 著者版 Theorem 6.4 の本体の結晶の橋を普遍基底へ特殊化する。 -/
abbrev universalWittBigBridge := wittBigBridge (U.{u} p) (universalPrime_mul_injective.{u} p) (universalOrientedPrism_mod_generator_p_regular.{u} p) (universalResidue_natCast_unit.{u} p) (universalOrientedPrism_bounded (p := p))

/-- BS 著者版 Construction 4.18 の有限枠から大きい枠への既存の比較。 -/
abbrev universalAffineCechFrame (Q : Poly (residueU.{u} p)) :=
  affineCechAlexanderFrame (P := (U.{u} p)) (universalOrientedPrism_bounded (p := p)) Q

abbrev universalTwist :=
  polyUnderlying (E := E) (U.{u} p) (universalOrientedPrism_bounded (p := p)) ≫
    completeChange (E := E) p ((qU p).comp (U p).deltaStructure.frobeniusLift)

@[no_expose] def wittPrismBounded : IsBoundedPrism (universalWittCrystallinePrism.{u} p) := by
  unfold universalWittCrystallinePrism
  apply crystallineBounded p _
  simp only [wittCrystallinePrism, OrientedPrism.crystalline_generator]
abbrev wittPolynomial (n : ℕ) := polynomialDelta (E := E) (universalWittCrystallinePrism.{u} p) (wittPrismBounded p) n

def psiBaseChange (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((polyUnderlying (E := E) (U p) (universalOrientedPrism_bounded (p := p)) ≫
      completeChange (E := E) p (psiRing (U p) (universalPrime_mul_injective.{u} p))).app _ (polyPoint (residueU.{u} p) n)) (wittPolynomial (E := E) p n) := by
  have hc := prismaticCohomology_baseChange' (E := E) (U p) (universalOrientedPrism_bounded (p := p)) n
    (universalWittCrystallinePrism p) (wittPrismBounded p) (universalWittPrismMap p)
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
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (completeChange (E := E) p g ≫ completeChange (E := E) p h) (completeChange (E := E) p (h.comp g)) := by
  sorry -- cAlgBaseChange の合成（随伴の合成）と、primeAlgCompletion の後の底変換の完備化は元の完備底変換

/-- 概要：A₀ 上の Δ_0（A2 の `polyUnderlying`）は大きい Čech–Alexander 模型の Tot_{E∞} と関手 ∞ 圏で同型（BS 著者版 Construction 4.18 ＋ 脚注 10 を
Q について自然に）。
方針：A2 の `polyDeltaData` の docstring どおり、Δ_0 の ∞ 関手としての整合性は大きい模型の厳密な関手性から nerve で作る：
`strictShapeNerve (bigCechAlexander p) ≫ totEInfinityFunctor` を、各頂点での同型（A0 の `prismaticCohomology_eq_cechAlexanderTot` の CAlg 版、
Shared の `derivedGlobalSectionsCAlg_eq_totEInfinity`：site の RΓ の錐を Čech 脈体へ制限、`isLimitCone_iff_restrict_cech`）に沿って
頂点を RΓ に差し替えたものが `polyDeltaData.val`（Joyal の isofibration Fun(K, X) → Fun(sk₀K, X)）。この同型はその構成から出る。
規約：**要相談**：A2 の `PolyDeltaData` にこの同型を欄として持たせるか（今は val・obj_eq・map_eval だけ）。
使われ方：`bigZigzagIso` の段 1。 -/
def polyUnderlying_iso_bigCech :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (polyUnderlying (E := E) (U.{u} p) (universalOrientedPrism_bounded (p := p)))
      (Cosimplicial.strictShapeNerve (bigCechAlexander (U p) (universalOrientedPrism_bounded (p := p))) ≫ Cosimplicial.totEInfinityFunctor (E := E) _) := by
  sorry -- A2 の polyDeltaData を大きい模型から頂点の差し替えで作り、その差し替えの同型（要相談：A2 側の欄）

/-- BS 著者版 Theorem 6.4 の普遍基底の大きい模型から一般pd関手への自然変換。 -/
def universalWittToPdModel : universalWittPdFunctor.{u} p ⟶
    pdModelPolynomialFunctor p (residueU p) ⋙ Cosimplicial.restrictCosimplicial (wZero p (residueU p)) := by
  sorry -- 各 (Q, n) で pd 包の lift（x_{(q,i)} ↦ copy i の q、基底 w₀）。自然性は lift の一意性

/-- BS 著者版 Theorem 6.4 の有限枠における一般pd関手への射の両立。 -/
theorem universalWittToPdModel_frame (Q : Poly (residueU.{u} p)) :
    universalWittSmallFrame p Q ≫ (universalWittToPdModel p).app Q = pdModelBaseChange p (WU p) (residueU p) Q.n := by
  sorry -- pd 包の lift の一意性：X_j ↦ x_{X_j} ↦ X_j

theorem wittPdIdeal_le_bigResidue (Q : Poly (residueU.{u} p)) :
    wittPdIdeal p (residueU p) ≤ RingHom.ker (algebraMap (WU.{u} p) (bigResidue (U p) Q)) := by
  sorry -- J = w₀⁻¹(pC) は Q^∧/p で零

/-- 概要：完備係数変換と Tot の随伴の転置：厳密な自然変換 α : F ⟶ G ⋙ g_*（F は k 上、G は l 上）から、関手 ∞ 圏の辺
（completeChange g ∘ Tot_k ∘ F ⟹ Tot_l ∘ G）を実際のホモトピーとして。
方針：`strictNatTransHomotopy α` を Tot_k に後合成し、`totEInfinity_restrict`（Tot と係数制限の可換）で Tot_k ∘ g_* ∘ G を g^* ∘ Tot_l ∘ G に移し、
`cAlgBaseChange_restrictScalars_adjunction` の余単位と完備化の反射（G の Tot は p 完備）で転置する（関手 ∞ 圏の随伴は後合成で延びる）。
規約：G の各値の Tot は p 完備（仮定）。
使われ方：`bigZigzagIso` の段 2（g = ψ）・段 3（g = w₀）。 -/
def baseChangeTotHomotopy {k l : Type u} [CommRing k] [CommRing l] (g : k →+* l) {𝒞 : Type u} [SmallCategory 𝒞]
    {F : 𝒞 ⥤ Cosimplicial.CosimplicialAlgebra k} {G : 𝒞 ⥤ Cosimplicial.CosimplicialAlgebra l}
    (α : F ⟶ G ⋙ Cosimplicial.restrictCosimplicial g)
    (hG : ∀ c : 𝒞, completeAt (p : l) ((E.forget l).app _ (Cosimplicial.totEInfinity (E := E) l (G.obj c)))) :
    SSet.Homotopy (Cosimplicial.strictShapeNerve F ≫ Cosimplicial.totEInfinityFunctor (E := E) k ≫ completeChange (E := E) p g)
      (Cosimplicial.strictShapeNerve G ≫ Cosimplicial.totEInfinityFunctor (E := E) l) := by
  sorry -- 後合成・totEInfinity_restrict・随伴の転置（関手 ∞ 圏へ後合成で延ばした随伴）

/-- 概要：一つの射についての同じ転置：X → g_* Y から辺 completeChange g (Tot_k X) → Tot_l Y。 -/
def baseChangeTotEdge {k l : Type u} [CommRing k] [CommRing l] (g : k →+* l)
    {X : Cosimplicial.CosimplicialAlgebra k} {Y : Cosimplicial.CosimplicialAlgebra l}
    (α : X ⟶ (Cosimplicial.restrictCosimplicial g).obj Y)
    (hY : completeAt (p : l) ((E.forget l).app _ (Cosimplicial.totEInfinity (E := E) l Y))) :
    SSet.Edge ((completeChange (E := E) p g).app _ (Cosimplicial.totEInfinity (E := E) k X)) (Cosimplicial.totEInfinity (E := E) l Y) := by
  sorry -- totEInfinity_map α、totEInfinity_restrict の成分、随伴の余単位

/-- 概要：`baseChangeTotHomotopy` の頂点での辺は成分の `baseChangeTotEdge`（可逆性が一致）。 -/
theorem baseChangeTotHomotopy_vertex {k l : Type u} [CommRing k] [CommRing l] (g : k →+* l) {𝒞 : Type u} [SmallCategory 𝒞]
    {F : 𝒞 ⥤ Cosimplicial.CosimplicialAlgebra k} {G : 𝒞 ⥤ Cosimplicial.CosimplicialAlgebra l}
    (α : F ⟶ G ⋙ Cosimplicial.restrictCosimplicial g)
    (hG : ∀ c : 𝒞, completeAt (p : l) ((E.forget l).app _ (Cosimplicial.totEInfinity (E := E) l (G.obj c)))) (c : 𝒞) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (baseChangeTotHomotopy (E := E) p g α hG) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).toTruncated ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (baseChangeTotEdge (E := E) p g (α.app c) (hG c)).toTruncated := by
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
    (hY : completeAt (p : l) ((E.forget l).app _ (Cosimplicial.totEInfinity (E := E) l Y)))
    (hY' : completeAt (p : l) ((E.forget l).app _ (Cosimplicial.totEInfinity (E := E) l Y'))) :
    HomotopyCategory.homMk ((Cosimplicial.totEInfinity_map (E := E) k a).map (completeChange (E := E) p g)) ≫
        HomotopyCategory.homMk (baseChangeTotEdge (E := E) p g α' hY') =
      HomotopyCategory.homMk (baseChangeTotEdge (E := E) p g α hY) ≫
        HomotopyCategory.homMk (Cosimplicial.totEInfinity_map (E := E) l b) := by
  sorry -- totEInfinity_map の関手性（h を nerve の 2 単体に）と余単位の自然性

theorem wittBigPdModel_complete (Q : Poly (residueU.{u} p)) :
    completeAt (p : WU.{u} p) ((E.forget _).app _ (Cosimplicial.totEInfinity (E := E) _ ((universalWittPdFunctor p).obj Q))) := by
  sorry -- 各項は p 完備（IsCompletedPDEnvelope.complete）、Δ 上の極限は完備性を保つ
theorem pdModel_complete (k : Type u) [CommRing k] (hk : IsAdicComplete (Ideal.span {(p : k)}) k) (r : ℕ) :
    completeAt (p : k) ((E.forget k).app _ (Cosimplicial.totEInfinity (E := E) k (pdModel p k r))) := by
  sorry -- 各項は p 完備化、極限は完備性を保つ

/-! ### 各対象での可逆性（小さい模型の結果を「表示によらない」で移す、§10.5 の 5） -/

theorem cechAlexanderFrame_isInvertible (Q : Poly (residueU.{u} p)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (Cosimplicial.totEInfinity_map (E := E) _ (universalAffineCechFrame p Q)).toTruncated := by
  sorry -- 両方とも Δ_{Q^∧/A₀} の Čech 脈体（A2 の prismaticCohomologyCAlg_eq_totEInfinity と A0 の
        -- prismaticCohomology_eq_cechAlexanderTot）。枠の射は site の対象の射なので制限の錐と両立し、Tot の上で可逆

theorem wittSmallFrame_isInvertible (Q : Poly (residueU.{u} p)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (Cosimplicial.totEInfinity_map (E := E) _ (universalWittSmallFrame p Q)).toTruncated := by
  sorry -- pdCechNerveMap_quasiIso（どちらの枠も Q^∧/p を覆う、W は p 完備）と totEInfinity_map_isInvertible

/-- 概要：小さい模型での結晶の橋 C_small(n)^• → ψ_* pdModel(W, n)^•（X ↦ X^p、A₀ → W は ψ）。
方針：各項で envelope の lift（δ 射 X ↦ X^p、基底 ψ。pdModel W n の δ 構造は δ(X) = 0 の延長）。
規約：原典の η ではなく、η から δ 変数を収縮した形：W 上では A1/CrystallineSite の `frobeniusPdBridge`（(A, I) = (W(C), J) の
`etaBridge ≫ pdDeltaRetraction`）を `pdModel_iso_pdCechNerve` で pdModel W n に移したもの（ψ に沿う C_small の底変換を前に合成）。
型は δ 変数なしの pdModel W n への写像のまま（大きい模型 `wittBigPdModel` が δ 変数なしで、`wittBridge_frame_comm` を X ↦ x^p で書くため）。
使われ方：`wittSmallBridge_isInvertible`、`wittBridge_frame_comm`。 -/
def wittSmallBridge (n : ℕ) :
    polyCosimplicialAlgebra (U.{u} p) (universalOrientedPrism_bounded (p := p)) n ⟶
      (Cosimplicial.restrictCosimplicial (psiRing (U p) (universalPrime_mul_injective.{u} p))).obj (pdModel p (WU p) n) := by
  sorry -- 各項で envelope の lift（δ 射 X ↦ X^p、基底 ψ）

/-- 概要：小さい模型の原典 Thm 6.4 の核心（ψ に沿う底変換 ＋ Thm 5.2 β）：転置した辺 completeChange ψ (Tot C_small(n)) → Tot pdModel(W, n) は可逆。
方針：`psiBaseChange`（Cor 4.12）と A0 の `cechAlexanderAffine_baseChange` で左辺を W 上の Čech–Alexander 模型 C_W(T′)^• の Tot に、
W 上の Thm 5.2：A1/CrystallineSite の `crystallineComparison_polynomial`（(A, I) = (W(C), J)、比較写像は原典の η `etaBridge` と
δ 変数の収縮 `pdDeltaRetraction` の Tot）を `frobeniusPdBridge_tot` で X ↦ X^p の写像（`frobeniusPdBridge`）の Tot の可逆性に読み、
`pdModel_iso_pdCechNerve` で pdModel W n へ移す（(a) の同型は可逆なので 2-out-of-3 で外れる）。旧 `wittPdBridge`（VertexIso の存在）を
この辺の可逆性に置き換えた。
規約：Frobenius との両立は使わない。
使われ方：`wittBigBridge_isInvertible`。 -/
theorem wittSmallBridge_isInvertible (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (baseChangeTotEdge (E := E) p (psiRing (U p) (universalPrime_mul_injective.{u} p)) (wittSmallBridge.{u} p n)
      (pdModel_complete (E := E) p (WU p) (by sorry) n)).toTruncated := by
  sorry -- psiBaseChange・cechAlexanderAffine_baseChange・crystallineComparison_polynomial（(W, J)）・frobeniusPdBridge_tot・
        -- pdModel_iso_pdCechNerve（W の p 完備性の sorry は wittCrystallinePrism と同じ根拠）

theorem wittBridge_frame_comm (Q : Poly (residueU.{u} p)) :
    wittSmallBridge p Q.n ≫ (Cosimplicial.restrictCosimplicial (psiRing (U p) (universalPrime_mul_injective.{u} p))).map (universalWittSmallFrame p Q) =
      universalAffineCechFrame p Q ≫ (universalWittBigBridge p).app Q := by
  sorry -- envelope の lift の一意性：両辺とも X_j^{(i)} ↦ φ(x_{(X_j,i)}) = x_{(X_j,i)}^p の δ 射

/-- 概要：段 2 の成分は可逆。
方針：`baseChangeTotEdge_natural`（`wittBridge_frame_comm`）の四角形で、`cechAlexanderFrame_isInvertible`（の完備係数変換）・
`wittSmallBridge_isInvertible`・`wittSmallFrame_isInvertible` から 2-out-of-3。 -/
theorem wittBigBridge_isInvertible (Q : Poly (residueU.{u} p)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (baseChangeTotEdge (E := E) p (psiRing (U p) (universalPrime_mul_injective.{u} p)) ((universalWittBigBridge p).app Q) (wittBigPdModel_complete (E := E) p Q)).toTruncated := by
  sorry -- 四角形と 2-out-of-3

/-- 概要：小さい模型の係数変換は Tot で可逆（完備底変換と Tot が可換）。
方針：W 上と C 上の de Rham 比較（`pdDeRhamFunctorIso` の成分）は係数変換と厳密に両立し、Ω̂^•_{W⟨X⟩} ⊗̂_W C ≅ Ω̂^•_{C⟨X⟩}（各次数有限自由、有界）。 -/
theorem pdModelBaseChange_isInvertible (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (baseChangeTotEdge (E := E) p (wZero p (residueU p)) (pdModelBaseChange.{u} p (WU p) (residueU p) n)
      (pdModel_complete (E := E) p (residueU p) (by sorry) n)).toTruncated := by
  sorry -- de Rham の span（行 0・列 0 の射影）は係数変換と可換、有界で有限自由な Ω の完備底変換
        -- （C の p 完備性の sorry は C = A₀/d₀ が有界 prism の剰余であることから）

/-- 概要：段 3 の成分は可逆。
方針：`baseChangeTotEdge_natural`（a = `wittSmallFrame`、b = 𝟙、`wittToSmall_frame`）で `pdModelBaseChange_isInvertible` と
`wittSmallFrame_isInvertible` から 2-out-of-3。 -/
theorem wittToSmall_isInvertible (Q : Poly (residueU.{u} p)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (baseChangeTotEdge (E := E) p (wZero p (residueU p)) ((universalWittToPdModel p).app Q)
      (pdModel_complete (E := E) p (residueU p) (by sorry) Q.n)).toTruncated := by
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
def bigZigzagIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (universalTwist.{u} (E := E) p) (theoryFormsCAlg (E := E) p (residueU p)) := by
  let hU := universalOrientedPrism_bounded (p := p)
  let Δ0 := polyUnderlying (E := E) (U.{u} p) hU
  let cψ := completeChange (E := E) p (psiRing (U.{u} p) (universalPrime_mul_injective.{u} p))
  let cw := completeChange (E := E) p (wZero.{u} p (residueU p))
  let SA := Cosimplicial.strictShapeNerve (bigCechAlexander (U.{u} p) (universalOrientedPrism_bounded (p := p)))
  let SD := Cosimplicial.strictShapeNerve (universalWittPdFunctor.{u} p)
  let S0 := Cosimplicial.strictShapeNerve (pdModelPolynomialFunctor p (residueU.{u} p))
  let TA := Cosimplicial.totEInfinityFunctor (E := E) (universalOrientedPrismRing.{u} p)
  let TW := Cosimplicial.totEInfinityFunctor (E := E) (WU.{u} p)
  let TC := Cosimplicial.totEInfinityFunctor (E := E) (residueU.{u} p)
  -- 段 0
  let e0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (universalTwist (E := E) p) (Δ0 ≫ cψ ≫ cw) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (completeChange_comp (E := E) p (psiRing (U p) (universalPrime_mul_injective.{u} p)) (wZero p (residueU p))).symm Δ0) (by dsimp only [universalTwist, Δ0]; rw [wZero_psi]) rfl
  -- 段 1
  let e1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Δ0 ≫ cψ ≫ cw) (SA ≫ TA ≫ cψ ≫ cw) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((polyUnderlying_iso_bigCech (E := E) p).postcomp (cψ ≫ cw)) rfl (by simp only [SA, TA, SD, TW, S0, TC, cψ, cw, Category.assoc])
  -- 段 2
  let e2 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SA ≫ TA ≫ cψ ≫ cw) (SD ≫ TW ≫ cw) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy
        (baseChangeTotHomotopy (E := E) p (psiRing (U p) (universalPrime_mul_injective.{u} p)) (universalWittBigBridge p) (wittBigPdModel_complete (E := E) p)) (by
          sorry)).postcomp cw) -- 頂点 ULift.up (nerveVertex Q) で baseChangeTotHomotopy_vertex と wittBigBridge_isInvertible
      (by simp only [SA, TA, SD, TW, S0, TC, cψ, cw, Category.assoc]) (by simp only [SA, TA, SD, TW, S0, TC, cψ, cw, Category.assoc])
  -- 段 3
  let e3 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SD ≫ TW ≫ cw) (S0 ≫ TC) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy
        (baseChangeTotHomotopy (E := E) p (wZero p (residueU p)) (universalWittToPdModel p) (fun Q => pdModel_complete (E := E) p (residueU p) (by sorry) Q.n)) (by
          sorry)) -- 頂点で baseChangeTotHomotopy_vertex と wittToSmall_isInvertible。C の p 完備性は上と同じ
      (by simp only [SA, TA, SD, TW, S0, TC, cψ, cw, Category.assoc]) rfl
  -- 段 4
  exact e0 ≪≫ e1 ≪≫ e2 ≪≫ e3 ≪≫ theoryPdDeRhamFunctorIso (E := E) p (residueU p)

/-- 概要：D69 の比較同型の各 n での成分（11-07、§10.5 の決定）：**大きい模型を通る zigzag の成分として定義し直した**。
方針：`bigZigzagIso` の `FunctorIso.app`。以前の定義（小さい模型の四本の脚 `WittComparisonLegs` の合成）は持ち上げの選択に依存し
関手にならないので外した。小さい模型の結果は各対象での可逆性（`wittSmallBridge_isInvertible` など）に使う。
規約：—
使われ方：`deRham_iso_polynomial_universal` の型の条件。 -/
def wittComposite (n : ℕ) := (bigZigzagIso.{u} (E := E) p).app (polyPoint _ n)

/-- 概要：A_0 上の比較同型（原典 Thm 6.4 の証明を A_0 で、D69）。成分は `wittComposite`。11-07：関手としての同型のまま（D69 の決定）。
方針：大きい模型の厳密な zigzag `bigZigzagIso`（a1-design §10.5）。成分の条件は `wittComposite` の定義から。
規約：`FunctorIso` は Fun(N(Poly), CAlg) のホモトピー圏の同型。高次の整合性は厳密な関手・自然変換の nerve から来る（§10.4 の (i)〜(iii)）。
使われ方：`transferWittComparison`。 -/
def deRham_iso_polynomial_universal :
    { e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (universalTwist.{u} (E := E) p) (theoryFormsCAlg (E := E) p (residueU p)) //
      ∀ n, e.app (polyPoint _ n) = wittComposite (E := E) p n } :=
  ⟨bigZigzagIso (E := E) p, fun _ => rfl⟩

variable {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)
abbrev modOrientation : A →+* modPrime p (A ⧸ P.ideal) :=
  (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ P.ideal)})).comp (Ideal.Quotient.mk P.ideal)
abbrev twistedReduction := (modOrientation p P).comp P.deltaStructure.frobeniusLift
abbrev reducedPolyDelta := polyUnderlying (E := E) P hP ≫ completeChange (E := E) p (twistedReduction p P)
abbrev reducedPolyForms := changePolyNerve (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ P.ideal)})) ≫
  theoryFormsCAlg (E := E) p (modPrime p (A ⧸ P.ideal))

/-- A₀ で既に構成した射を d₀↦d に沿って移す。 -/
abbrev residueToModP := (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ P.ideal)})).comp (orientationMap P).quotientMap

def universalDeltaChange (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((reducedPolyDelta (E := E) p P hP).app _ (polyPoint _ n))
    ((completeChange (E := E) p (residueToModP p P)).app _ ((universalTwist (E := E) p).app _ (polyPoint _ n))) := by
  sorry -- 分類射による polynomialChangeEdge は Cor 4.12 で可逆。
        -- δ 射と φ の両立、完備底変換の結合則でその逆を取る
def universalFormsChange (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((completeChange (E := E) p (residueToModP p P)).app _ (theoryFormsVertex (E := E) p (residueU p) n))
    ((reducedPolyForms (E := E) p P).app _ (polyPoint _ n)) := by
  sorry -- 有限自由な連続形式の底変換。座標とその微分を同じ座標へ送る

def transferWittComparison (hperf : P.deltaStructure.IsPerfect) :
    { e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (reducedPolyDelta (E := E) p P hP) (reducedPolyForms (E := E) p P) // ∀ n : ℕ,
      e.app (polyPoint _ n) = universalDeltaChange (E := E) p P hP n ≪≫
        ((deRham_iso_polynomial_universal (E := E) p).val.app (polyPoint _ n)).map (completeChange (E := E) p (residueToModP p P)) ≪≫
        universalFormsChange (E := E) p P n } := by
  sorry -- 普遍例で構成した比較を分類射に沿って移す。係数・多項式の持ち上げに関する
        -- J つき比較の自然性により各成分が多項式射と可換

def deRham_iso_polynomial_modP (hperf : P.deltaStructure.IsPerfect) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (reducedPolyDelta (E := E) p P hP) (reducedPolyForms (E := E) p P) :=
  (transferWittComparison (E := E) p P hP hperf).val

abbrev rootSource (C : Type u) [CommRing C] := theoryFormsVertex (E := E) p C 1
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

abbrev singleRootTarget (n : ℕ) := (SerrePositivity.EInfinity.discreteCDGA _).obj (rootTargetAlgebra p P n)

def singleTargetZeroIso (n : ℕ) :
    (singleRootTarget p P n).X.X 0 ≃+ (rootStrictTarget p P n) := by
  sorry -- HomologicalComplex.singleObjXSelf の底の加法同型

/-- BS 著者版 Theorem 6.4 の零次の多項式を、既存の零形式・完備化単位・複体延長の同型で読む。 -/
@[no_expose] def polynomialZeroFormInComplex (k : Type u) [CommRing k] (n : ℕ) (a : MvPolynomial (Fin n) k) :
    (formsCDGA p k n).X.X 0 := by
  let K := DeRham.completedDeRhamComplex k (formVars.{u} n) p
  let a' := MvPolynomial.rename (fun i : Fin n => (ULift.up i : formVars.{u} n)) a
  let ω := DeRham.completedFormsUnit k (formVars.{u} n) p 0
    (DeRham.formsZeroEquiv k (formVars.{u} n) a')
  let e := K.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) rfl
  change (K.extend ComplexShape.embeddingUpNat).X (0 : ℤ)
  exact e.inv.hom (show K.X 0 from ω)

def cdgaAugmentation (n : ℕ) :
    let C := modPrime p (A ⧸ P.ideal)
    { f : formsCDGA p C n ⟶ singleRootTarget p P n //
      ∀ a : MvPolynomial (Fin n) C, singleTargetZeroIso p P n
        (f.hom.hom.f 0 (polynomialZeroFormInComplex p C n a)) = rootDegreeZeroMap p P n a } := by
  sorry -- 次数零は rootDegreeZeroMap（p=0）、正次数では標的が零。
        -- 単位・外積・微分に両立する CommMon の射を作る

def rootFormsAugmentation (n : ℕ) :
    SSet.Edge (theoryFormsVertex (E := E) p (modPrime p (A ⧸ P.ideal)) n)
      ((E.discrete _).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (rootTargetAlgebra p P n))) := by
  let C := modPrime p (A ⧸ P.ideal)
  let B := rootTargetAlgebra p P n
  let e := (nerve.edgeMk (cdgaAugmentation p P n).val).map (E.ofCdga C)
  let i := (E.ofCdga_discrete C).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B)
  have hn : (nerveMap (discreteCDGA C) ≫ E.ofCdga C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B) =
      (E.ofCdga C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((discreteCDGA C).obj B)) := by
    exact congrArg ((E.ofCdga C).app (Opposite.op ⦋0⦌)) (nerveMap_app_mk₀ (discreteCDGA C) B)
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((E.ofCdga C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((discreteCDGA C).obj B)))
      ((E.discrete C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B)) := by
    simpa only [hn] using i
  let a := Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _
    (SSet.HomotopyCategory.homMk e ≫ hi.hom))
  have hs : theoryFormsVertex (E := E) p C n =
      (E.ofCdga C).app (Opposite.op ⦋0⦌) (nerveEquiv.symm (formsCDGA p C n)) := by
    change (E.ofCdga C).app (Opposite.op ⦋0⦌)
      ((Cosimplicial.strictShapeNerve (formsCDGAFunctor p C)).app (Opposite.op ⦋0⦌) (polyPoint C n)) = _
    apply congrArg ((E.ofCdga C).app (Opposite.op ⦋0⦌))
    apply ComposableArrows.ext₀
    rfl
  exact SSet.Edge.mk a.edge (by rw [hs]; exact a.src_eq)
    (by convert a.tgt_eq using 1 <;> rfl)

def rootArrow (n : ℕ) : ofAlgebra (A ⧸ P.ideal) (polyAlgebra p (A ⧸ P.ideal) n) ⟶
    ofAlgebra (A ⧸ P.ideal) (polyRootAlgebra p (A ⧸ P.ideal) n) :=
  Under.homMk (CommRingCat.ofHom (polyAlgebraToRoot p _ n)) (by sorry) -- 両端の係数を保つ
abbrev rootDeltaEdge (n : ℕ) := (nerve.edgeMk (rootArrow p P n)).map
  (derivedPrismaticCohomologyDiscrete (E := E) P hP ≫ prismCompleteInclusion (E := E) P ≫ completeChange (E := E) p (twistedReduction p P))

/-- 完備離散入力 T での値を polyUnderlying の多項式頂点に移送する。 -/
def completedPolynomialRecovery (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((derivedPrismaticCohomologyDiscrete (E := E) P hP ≫ prismCompleteInclusion (E := E) P ≫
      completeChange (E := E) p (twistedReduction p P)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra _ (polyAlgebra p (A ⧸ P.ideal) n))))
      ((reducedPolyDelta (E := E) p P hP).app _ (polyPoint _ n)) := by
  sorry -- A2 の polyRecovery、離散多項式の p 完備化は有界ねじれで次数零、D32

theorem deRham_iso_rootAlgebra_modP (hperf : P.deltaStructure.IsPerfect) (n : ℕ) :
    let g := rootFormsAugmentation (E := E) p P n
    let e := completedPolynomialRecovery (E := E) p P hP n ≪≫ (deRham_iso_polynomial_modP (E := E) p P hP hperf).app (polyPoint _ n)
    ∃ eInf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((derivedPrismaticCohomologyDiscrete (E := E) P hP ≫ prismCompleteInclusion (E := E) P ≫
        completeChange (E := E) p (twistedReduction p P)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra _ (polyRootAlgebra p (A ⧸ P.ideal) n))))
        ((E.discrete _).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (rootTargetAlgebra p P n))),
      HomotopyCategory.homMk (rootDeltaEdge (E := E) p P hP n) ≫ eInf.hom = e.hom ≫ HomotopyCategory.homMk g := by
  sorry -- X_j↦X_j^p の列の完備 filtered 余極限。mod p で正次数の形式の遷移は零、
        -- 次数零は T∞/p。最初の余極限脚で可換式を得る


end SerrePositivity.BhattScholze.Prismatic
