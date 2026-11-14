-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.HodgeTateComparison（仮。原典 §6 Construction 6.1・Prop 6.2・Thm 6.3、§4.2 Cor 4.12・Lemma 4.10、Ex 2.21・3.4）
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md §2.4・§2.5・§3、単位 A1-4。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.HomologicalAlgebra.CochainCompleteTorAmplitude
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoverCompleteTor
public import SerrePositivity.BhattScholze.Delta.CompleteRegularity.RelativeCompleteRegularity

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateCartierAssembly
public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaRing
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaLocalization
public import SerrePositivity.BhattScholze.Delta.Distinguished.Distinguished
public import SerrePositivity.BhattScholze.Delta.Division.Basic
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoverCompleteTor
-- 本ファイルは drafts/A0/{PrismaticSite,PrismaticEnvelope,CechAlexander}.lean、drafts/A1/{HodgeTateMap,CrystallineInput}.lean、drafts/Shared/DeRhamPolynomial.lean を import する。
-- 結晶側の計算（D68 改訂後：Lemma 5.4・pd Poincaré・BdJ・Cartier の mod p の直接証明）は drafts/A1/CrystallineInput.lean（本ファイルより先）。DeRhamComparisonPoly は本ファイルより後。

/-!
# Hodge–Tate 比較の証明の骨組み（BS 著者版 Construction 6.1、Prop 6.2、Thm 6.3、Cor 4.12、Lemma 4.10）

## 概要
一般の有界向き付き prism (A,(d)) と R = (A/d)⟨X_1,…,X_r⟩ について、HT 比較の写像 η^*（`HodgeTateMap`）が同型であることを、原典 §6 の帰着で示す：
(a) 結晶 prism は Cor 5.5、(b) 普遍向き付き prism (A_0,(d)) は Construction 6.1 の α : (A_0,(d)) → (D_0,(p)) で (a) へ、
(c) 一般の (A,(d)) は d の選択による A_0 → A と、底変換関手 b̂^*・ĉ^* の保存性・Rem 4.19 の複体の項ごとの一致・Lemma 4.22 で (Z_p,(p)) へ。
**結晶側の入力は一つの定理 `hodgeTate_iso_polynomial_Zp`（(Z_p,(p))、R = F_p[X_1,…,X_r] の Cor 5.5）に閉じ込める**。その証明（D68 改訂後：
Lemma 5.4、C^•/p → D^•/p ← D_0^•/p、pd 包の Čech 脈体と de Rham 複体の比較、Cartier 同型、すべて mod p）は A1/CrystallineInput（A1-2・A1-3、a1-design §10）。

## 方針
原典の単体的可換環 E = A ⊗̂^L_{A_0} D_0 は作らない（D30）：b̂^* := â^* ∘ Res_{A_0}、ĉ^* := â^* ∘ Res_{A_0} ∘ (− ⊗^L_{Z_p} A)。
普遍向き付き prism は Ex 2.21（Z_(p){d, δ(d)^{-1}}）の (p,d) 完備化（Ex 3.4）。

## 規約
基底は向き付き（D19）。R は p 完備化した多項式代数（D29）。模型は Rem 4.19 の小さい模型。Lean の名前は仮。

## 使われ方
A2（Construction 7.6）、A5（Prop 8.5、Lemma 8.6）、A7（Prop 8.13）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial TensorProduct

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.DerivedCompletion SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable {p : ℕ} [Fact p.Prime]

/-! ## 結晶側の計算から導く HT 比較（D68 改訂 11-05 夜：黒箱を外し、A1/CrystallineInput の六段で mod p に直接証明。恒久の引用なし） -/

-- hodgeTate_iso_polynomial_Zp は本体の HodgeTateCartierAssembly に置く。

/-! ## Cor 5.5：結晶 prism -/

/-- 概要：Cor 5.5：結晶 prism (A,(p)) と S = A/p[X_1,…,X_r]^∧ について η^* は同型。
方針：A は p ねじれなし（prism の生成元 p は正則）なので Z_p → A は平坦、Lemma 4.20（Tor 振幅 0）で (Z_p,(p)) に底変換し、
`hodgeTate_iso_polynomial_Zp`。η^* の底変換との両立は生成元で。
規約：`OrientedPrism.crystalline`。
使われ方：Prop 6.2 (a)(b)。 -/
theorem hodgeTate_iso_crystalline {A : Type u} [CommRing A] (P : OrientedPrism p A)
    (hcrys : P.generator = (p : A)) (r : ℕ) :
    HodgeTateIsoStatement P (crystallineBounded p P hcrys) r := by
  sorry -- Z_p→A は平坦。Lemma 4.20 の標準脚と Bockstein を使い η⁰・η¹、外積で η^i を移す

/-! ## 普遍向き付き prism（Ex 2.21、Ex 3.4、G-A1-12） -/

/-- 概要：Ex 2.21：distinguished 元 d をもつ普遍 δ 環 Z_(p){d, δ(d)^{-1}}。
方針：Z_(p) 上の一変数自由 δ 環（`RelativeFreeDeltaRing Unit`）を δ(d) で局所化（`DeltaStructure.localization`）。
規約：普遍性：δ 環 B と distinguished な b ∈ B に対し、d ↦ b の δ 射が一意（δ(b) が単元なので局所化を経由）。
使われ方：A_0 の定義。 -/
abbrev freeOrientationRing := FreeDeltaRing PUnit.{u+1}
abbrev freeOrientation : freeOrientationRing.{u} := MvPolynomial.X (PUnit.unit, 0)
abbrev freeOrientationDelta (p : ℕ) [Fact p.Prime] := freeDeltaStructure p PUnit.{u+1}

/-- ℤ_(p) の分母と δ(d) を逆にし、δ 局所化のため Frobenius で閉じる。 -/
def orientationDenominators (p : ℕ) [Fact p.Prime] : Submonoid freeOrientationRing.{u} :=
  Submonoid.closure (insert ((freeOrientationDelta p).delta freeOrientation)
    (Set.range (fun n : {n : ℕ // Nat.Coprime n p} => (n.val : freeOrientationRing))))

-- D77：普遍 prism の実装は K2 の本体を直接使う。
abbrev universalDistinguishedRing (p : ℕ) [Fact p.Prime] := UniversalDistinguishedRing.{u} p
abbrev distinguishedDelta (p : ℕ) [Fact p.Prime] := universalDistinguishedDelta.{u} p
abbrev rawOrientation (p : ℕ) [Fact p.Prime] := universalDistinguishedGenerator.{u} p
abbrev universalOrientedPrismRing (p : ℕ) [Fact p.Prime] := UniversalOrientedPrismRing.{u} p
abbrev universalOrientedPrism (p : ℕ) [Fact p.Prime] :=
  BhattScholze.universalOrientedPrism.{u} p

/-- Ex 3.4 の有界性。普遍 Frobenius には d 完全平坦性だけを使う（D77）。 -/
theorem universalOrientedPrism_bounded : IsBoundedPrism (universalOrientedPrism (p := p)) :=
  BhattScholze.universalOrientedPrism_bounded p

abbrev modPrime (p : ℕ) (A : Type u) [CommRing A] := A ⧸ Ideal.span {(p : A)}

def modPrimeFrob (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] : modPrime p A →+* modPrime p A := by
  classical
  by_cases h : Subsingleton (modPrime p A)
  · exact RingHom.id _
  · letI : Nontrivial (modPrime p A) := not_subsingleton_iff_nontrivial.mp h
    letI : CharP (modPrime p A) p := by sorry -- p は素数で商では零、商は非自明
    exact frobenius _ p

def FrobeniusFlatModP (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] : Prop :=
  letI : Module (modPrime p A) (modPrime p A) := Module.compHom _ (modPrimeFrob p A)
  Module.Flat (modPrime p A) (modPrime p A)

-- D77：普遍 prism の通常の Frobenius 平坦性は主張しない。
-- K2 の universalOrientedPrism_frobenius_isCompletelyFlat を直接入力する。

/-- 概要：普遍性：任意の向き付き prism (A,(d_A)) に対し、d ↦ d_A の prism の射 A_0 → A が一意。
方針：d_A は distinguished（`OrientedPrism.isDistinguished_generator`）なので δ(d_A) は単元、自由 δ 環と局所化の普遍性、A の (p,d) 完備性で
完備化を経由。
規約：—
使われ方：Prop 6.2 (c) の b。 -/
theorem universalOrientedPrism_hom {A : Type u} [CommRing A] (P : OrientedPrism p A) :
    ∃! f : OrientedPrism.Hom (universalOrientedPrism.{u} (p := p)) P,
      f.toRingHom (universalOrientedPrism.{u} (p := p)).generator = P.generator := by
  exact existsUnique_universalOrientedPrismHom p P

/-! ## Construction 6.1

D77：環・prism・標準射と非有界な鎖複体の振幅の入力は本体の
`Construction61Frobenius`・`CrystallineCover*` にある。
以下の ∞ 圏の保存性と HT 比較の組み立ては G10 の後に接続する。
-/

variable {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-! D20。Def 2.42 は Koszul ホモロジーの底変換を全次数で検査する。 -/

abbrev koszulResidue {T : Type u} [CommRing T] {r : ℕ} (x : Fin r → T) := T ⧸ Ideal.span (Set.range x)
abbrev relBaseSequence := ![(p : A), P.generator]
def relSequence {B : Type u} [CommRing B] [Algebra A B] {r : ℕ} (x : Fin r → B) : Fin (2+r) → B :=
  Fin.addCases (algebraMap A B ∘ relBaseSequence P) x
def relResidueMap {B : Type u} [CommRing B] [Algebra A B] {r : ℕ} (x : Fin r → B) :
    koszulResidue (relBaseSequence P) →+* koszulResidue (relSequence P x) :=
  Ideal.quotientMap _ (algebraMap A B) (by sorry) -- 最初の二生成元の像

def relHomologyBaseChange {B : Type u} [CommRing B] [Algebra A B] {r : ℕ} (x : Fin r → B) (j : ℕ) :
    let k := koszulResidue (relBaseSequence P)
    let S := koszulResidue (relSequence P x)
    letI : Algebra k S := (relResidueMap P x).toAlgebra
    letI := koszulResidueModule (relBaseSequence P) (j : ℤ)
    letI := koszulResidueModule (relSequence P x) (j : ℤ)
    S ⊗[k] ((koszulComplex (relBaseSequence P)).homology (j : ℤ)) →ₗ[S]
      ((koszulComplex (relSequence P x)).homology (j : ℤ)) := by
  sorry -- 係数を送り最初の二つの Koszul 因子を包含した鎖写像の H_j を S 線形に延長

/-- A0 の IsCompletelyRegularRel 用の D20 の右辺。H₀ の平坦性だけでは足りない。 -/
def FlatKoszulComparison {B : Type u} [CommRing B] [Algebra A B] {r : ℕ} (x : Fin r → B) : Prop :=
  let k := koszulResidue (relBaseSequence P)
  let S := koszulResidue (relSequence P x)
  letI : Algebra k S := (relResidueMap P x).toAlgebra
  Module.Flat k S ∧ ∀ j, Function.Bijective (relHomologyBaseChange P x j)

/-- 概要：Construction 6.1 の仮定：A/p の Frobenius が平坦、A/d が p ねじれなし。
方針：述語。
規約：原典の通常の平坦性を保つ。普遍例はこの構造を経由せず、D77 の二つの入力を使う。
使われ方：原典どおりの仮定の記録。本体の適用は D77 の二入力で行う。 -/
structure Construction61Hypotheses : Prop where
  frobenius_flat : FrobeniusFlatModP p A
  quotient_p_torsionFree : ∀ x : A ⧸ P.ideal, (p : A ⧸ P.ideal) * x = 0 → x = 0

-- H1 の古典的な構成は本体の同じ模型を使う。環・prism・射は入力の証明に依存しない。
abbrev coverDivision := Construction61.coverDivision P
abbrev coverDivisionMap := Construction61.coverDivisionMap P
abbrev crystallineCoverRing := Construction61.crystallineCoverRing P
abbrev coverBase := Construction61.coverBase P
abbrev crystallineCover := Construction61.crystallineCover P
abbrev crystallineCoverMap := Construction61.crystallineCoverMap P

/-- 結晶被覆の生成元は p。 -/
theorem crystallineCover_generator :
    (crystallineCover P).generator = (p : crystallineCoverRing P) := rfl

/-- D(A) の (p,d) 完備な頂点とその反射。 -/
abbrev CompleteModules := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
  (fun x => completeAt (p : A) x ∧ completeAt P.generator x)
instance : Quasicategory (CompleteModules P) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _
abbrev moduleInclusion : (CompleteModules P : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A := (CompleteModules P).ι
def moduleReflection : Σ L : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A ⟶ (CompleteModules P : SSet),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L (moduleInclusion P) := by
  sorry -- 要確認：DerivedGeneral/CompletionFunctor へ。(p,d) を指定した完備反射

def alphaStar :=
  moduleInclusion P ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange (crystallineCoverMap P).toRingHom ≫
    (moduleReflection (crystallineCover P)).1

def ReflectsEquivalences {X Y : SSet.{u+1}} (F : X ⟶ Y) : Prop :=
  ∀ {x y : X _⦋0⦌} (e : X.Edge x y), IsIso (HomotopyCategory.homMk (e.map F)) → IsIso (HomotopyCategory.homMk e)

/-- 概要：Construction 6.1 (1)：α̂^* は導来 (p,d) 完備な A 複体の上で保存的。
方針：mod p の分解 (6)：A/p → A/(p,d)（導来 Nakayama で保存的）→ A/(p,d^p)（Frobenius、忠実平坦）→ B/p = D_{(d)}(A/p)（pd 包、自由）。
規約：導来 Nakayama は G-A1-4。
使われ方：Prop 6.2 (b)(c)。 -/
theorem crystallineCoverMap_conservative (hF : IsCompletelyFlat
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) P.generator})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    ReflectsEquivalences (alphaStar P) := by
  sorry -- cofiber を mod p に落とし、(6) の d 完備 Nakayama と忠実平坦な Frobenius・pd 包を順に使う

/-! 完全Tor振幅は本体の `HasCochainCompleteTorAmplitude` に一本化する。
Construction 6.1の上界3は本体の非有界な半自由模型の評価そのものを使う。 -/

abbrev alphaModP := Construction61.alphaModP P

theorem torAmplitude_modP_le_one (hF : IsCompletelyFlat
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) P.generator})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) (n : ℤ)
    (K : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory (modPrime p A)) _⦋0⦌) (hK : Derived.IsCoconnectiveAt _ n K) :
    Derived.IsCoconnectiveAt _ (n-1) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange (alphaModP P)).app _ K) := by
  sorry -- 本体 Construction61.modPBaseChange_homology_isZero_below の半自由模型の評価を頂点に移す

theorem crystallineCoverMap_torAmplitude (hF : IsCompletelyFlat
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) P.generator})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    HasCochainCompleteTorAmplitude (crystallineCoverMap P).toRingHom ![(p : A), P.generator] 3 := by
  exact Construction61.crystallineCoverMap_torAmplitude P hF hR

theorem crystallineCoverMap_finiteTorAmplitude (hF : IsCompletelyFlat
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) P.generator})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    ∃ c : ℕ, HasCochainCompleteTorAmplitude (crystallineCoverMap P).toRingHom ![(p : A), P.generator] c :=
  ⟨_, crystallineCoverMap_torAmplitude P hF hR⟩

/-- 概要：Construction 6.1 (3)：α̂^*Δ_{R/A} ≃ Δ_{R_B/B}（Lemma 4.20）。
方針：Rem 4.19 の模型の項ごとの底変換と Lemma 4.22。
規約：—
使われ方：Prop 6.2 (b)。 -/
theorem crystallineCoverMap_prismaticCohomology (hP : IsBoundedPrism P) (hF : IsCompletelyFlat
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) P.generator})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) (r : ℕ) :
    PrismaticCohomologyBaseChangeStatement (E := E) P hP r (crystallineCover P)
      (by sorry) -- mod p では p=0
      (crystallineCoverMap P) := by
  sorry -- crystallineCoverMap_finiteTorAmplitude と A0 の項別比較を Lemma 4.22 で Tot に移す

/-! ## Prop 6.2（一般の r）と Thm 6.3 -/

/-- 概要：Prop 6.2 (b)：Construction 6.1 の仮定を満たす (A,(d)) について η^* は同型。
方針：α̂^* は保存的、α̂^*Δ_{R/A} ≃ Δ_{R_B/B}、(B,(p)) は結晶 prism で `hodgeTate_iso_crystalline`、α̂^*η^* が B 側の η^* に一致（生成元で）。
規約：—
使われ方：普遍向き付き prism への適用、Prop 6.2 (c)。 -/
theorem hodgeTate_iso_of_construction61 (hP : IsBoundedPrism P) (hF : IsCompletelyFlat
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) P.generator})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) (r : ℕ) :
    HodgeTateIsoStatement P hP r := by
  sorry -- α̂* は保存的。生成元で HT 写像を比較し結晶 prism 側の Cor 5.5 で検出

/-- 概要：底変換関手 b̂^*（b : A → E = A ⊗̂^L_{A_0} D_0 の読み替え）：Res_{A_0} の後に â^*（a = α_{A_0}）。
方針：D30。E は作らない。
規約：K は導来 (p,d) 完備な A 複体。
使われ方：Prop 6.2 (c)。 -/
abbrev orientationMap := (universalOrientedPrism_hom P).exists.choose
-- D77：universal61（通常の Frobenius 平坦性）は使わない。
-- 保存性・Tor の入力には、次の K2 の二定理を直接渡す。
abbrev universalFrobeniusInput (p : ℕ) [Fact p.Prime] :=
  universalOrientedPrism_frobenius_isCompletelyFlat.{u} p
abbrev universalPrimeInput (p : ℕ) [Fact p.Prime] :=
  universalOrientedPrism_mod_generator_p_regular.{u} p
abbrev universalCover (p : ℕ) [Fact p.Prime] := crystallineCover (universalOrientedPrism.{u} p)

def baseChangeB : (CompleteModules P : SSet) ⟶ (CompleteModules (universalCover.{u} p) : SSet) :=
  moduleInclusion P ≫ derivedInfinityRestrictScalars (E := E) (orientationMap P).toRingHom ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange (crystallineCoverMap (universalOrientedPrism.{u} p)).toRingHom ≫ (moduleReflection (universalCover p)).1

/-- 概要：底変換関手 ĉ^*（c : Z_p → E の読み替え）：(− ⊗^L_{Z_p} A) の後に Res_{A_0}、â^*。
方針：D30。
規約：—
使われ方：Prop 6.2 (c)。 -/
def baseChangeC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory (crystallineBase.{u} p) ⟶ (CompleteModules (universalCover.{u} p) : SSet) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange (padicCoefficientMap p P) ≫ derivedInfinityRestrictScalars (E := E) (orientationMap P).toRingHom ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange (crystallineCoverMap (universalOrientedPrism.{u} p)).toRingHom ≫ (moduleReflection _).1

/-- 概要：b̂^* は (p,d) 完備な A 複体の上で保存的（Res は完備性と零を保ち、â^* は保存的）。
方針：`crystallineCoverMap_conservative` を A_0 に。
規約：—
使われ方：Prop 6.2 (c)。 -/
theorem baseChangeB_conservative : ReflectsEquivalences (baseChangeB (E := E) P) := by
  sorry -- d を保つ分類射での制限は完備性と零を反映し、普遍 prism には K2 の universalFrobeniusInput と universalPrimeInput を直接渡す

/-- 概要：Rem 4.19 の複体の項ごとの一致 b̂^*C^n_{R/A} ≃ ĉ^*C^n_{F_p[X]/Z_p}、したがって b̂^*Δ_{R/A} ≃ ĉ^*Δ_{F_p[X]/Z_p}。
方針：C^n_A = C^n_{A_0} ⊗̂_{A_0} A、C^n_{A_0} ⊗̂_{A_0} D_0 = C^n_{D_0} = C^n_{Z_p} ⊗̂_{Z_p} D_0（A0 の `cechAlexanderAffine_baseChange`）、テンソルの結合則。
Tot と交換するのは Lemma 4.22（a は有限振幅、Z_p → A は Tor 振幅 ≤ 1、Res は完全）。
規約：—
使われ方：Prop 6.2 (c)。 -/
abbrev simplexShape := (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)
def affineModuleDiagram (hP : IsBoundedPrism P) (r : ℕ) : simplexShape.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A := by
  let D := polyCosimplicialAlgebra P hP r
  let N : simplexShape.{u} ⟶ nerve (BhattScholze.PerfectoidizationInterface.A_R A) :=
    { app := fun _ => ↾fun x => (D.mapComposableArrows _).obj x.down
      naturality := by sorry } -- 射列の同時制限
  exact N ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteEmbedding A

def affineCompleteDiagram (hP : IsBoundedPrism P) (r : ℕ) : simplexShape.{u} ⟶ (CompleteModules P : SSet) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (affineModuleDiagram P hP r) (by sorry) -- 各項の prism の (p,d) 完備性
def affineCompleteTot (hP : IsBoundedPrism P) (r : ℕ) : (CompleteModules P : SSet) _⦋0⦌ := by
  let x := prismaticCohomologyCAlg (E := E) P hP r
  exact ⟨(E.forget A).app _ x.val, by sorry⟩ -- x の完備性を忘却

/-- D30 で使用する二つの Tot 交換。保存性の対象は指定した cosimplicial 模型の極限錐。 -/
theorem baseChange_preserves_affineTot (hP : IsBoundedPrism P) (r : ℕ) :
    (∀ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (affineCompleteDiagram P hP r), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (c.postcomp (baseChangeB (E := E) P))) ∧
    (∀ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (affineModuleDiagram (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (c.postcomp (baseChangeC (E := E) P))) := by
  sorry -- Z_p→A は通常の Tor 振幅 ≤1、Res は極限を保つ。
        -- 完備底変換には Lemma 4.22 と crystallineCoverMap_finiteTorAmplitude を使う

theorem baseChange_cechAlexanderAffine_eq (hP : IsBoundedPrism P) (r : ℕ) :
    let Z := crystallineBasePrism.{u} p
    let hz := crystallineBaseBounded.{u} p
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (affineCompleteDiagram P hP r ≫ baseChangeB (E := E) P)
      (affineModuleDiagram Z hz r ≫ baseChangeC (E := E) P)) ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((baseChangeB (E := E) P).app _ (affineCompleteTot (E := E) P hP r))
        ((baseChangeC (E := E) P).app _ ((moduleInclusion Z).app _ (affineCompleteTot (E := E) Z hz r)))) := by
  sorry -- A0.cechAlexanderAffine_baseChange の二つの係数脚を copy ごとに比較。
        -- Lemma 4.22 と有限完全 Tor 振幅で同じ比較を Tot に移す

/-- 概要：Prop 6.2（一般の r）＝ Thm 6.3（多項式代数）：一般の有界向き付き prism (A,(d)) と R = (A/d)⟨X_1,…,X_r⟩ について η^* は同型。
方針：(a) 結晶：`hodgeTate_iso_crystalline`。(b)(c)：b̂^* が保存的、b̂^*η^* が ĉ^*（Z_p 側の η^*）に一致（生成元で）、Z_p 側は
`hodgeTate_iso_polynomial_Zp`。順序（W9-I-25）：r = 1 の加群の比較（η⁰・η¹）→ Lemma 4.10（`bockstein_sq_zero'`）→ 一般 r の dg 比較。
規約：D30。
使われ方：Cor 4.12、Lemma 4.10、A2・A5・A7。 -/
theorem affineLine_moduleComparison (hP : IsBoundedPrism P) :
    Function.Bijective (hodgeTateMapZero P hP 1) ∧ Function.Bijective (hodgeTateMapOne P hP 1) ∧
      ∀ i : ℕ, 1 < i → Subsingleton (hodgeTateCohomology' P hP 1 i) := by
  sorry -- η⁰・η¹ の基底の代表だけで加群の比較を作り、baseChangeB と Z_p の一変数
        -- Cartier 計算で検出する。この段階で η の外積への延長は用いない

theorem hodgeTate_iso (hP : IsBoundedPrism P) (r : ℕ) : HodgeTateIsoStatement P hP r := by
  sorry -- baseChangeB_conservative と項別比較で η の加群比較を検出。
        -- 一変数は η⁰・η¹ だけで H²=0、次に平方零、最後に r 変数で外積を使う

/-- 概要：Lemma 4.10：β(η^0 f)² = 0。
方針：r = 1 の `hodgeTate_iso` で H^2(Tot(C^•/d)) ≅ Ω^2 = 0、X ↦ f の関手性（Bockstein と cup 積の自然性）。
規約：—
使われ方：η^* の存在（`HodgeTateMap`）。循環ではない：Prop 6.2 の証明では η を D(R) の射として選ぶ（Ω^i は自由）ので η^* の存在を前提にしない。 -/
theorem bockstein_sq_zero' (hP : IsBoundedPrism P) (r : ℕ) : BetaSquareZero P hP r := by
  exact betaSquareZero_of_line P hP r ((affineLine_moduleComparison P hP).2.2 2 (by decide))

/-- 概要：Cor 4.12：Δ_{R/A} の形成は有界 prism の任意の射 (A,(d)) → (A′,(d′)) に沿う底変換と可換（Tor 振幅の仮定なし）。
方針：導来 Nakayama で mod d に帰着し、`hodgeTate_iso` と微分形式の底変換。
規約：—
使われ方：Construction 7.6 (4)（A2）。 -/
theorem prismaticCohomology_baseChange' (hP : IsBoundedPrism P) (r : ℕ)
    {A' : Type u} [CommRing A'] (P' : OrientedPrism p A') (hP' : IsBoundedPrism P') (f : OrientedPrism.Hom P P') :
    PrismaticCohomologyBaseChangeStatement (E := E) P hP r P' hP' f := by
  sorry -- 同じ polynomialChangeEdge を mod d で検査。Thm 6.3、完備形式の基底変換と導来 Nakayama

end SerrePositivity.BhattScholze.Prismatic
