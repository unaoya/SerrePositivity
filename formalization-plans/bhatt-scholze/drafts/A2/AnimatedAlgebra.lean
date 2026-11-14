-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Derived.AnimatedAlgebra（仮。原典 Construction 7.6 の始域、SAG 25.1.1.1）
-- 設計書：formalization-plans/bhatt-scholze/a2-design.md §2.1、単位 A2-1。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedFunctorRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaLeftKanExtension
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaLeftKanSiftedPreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaSiftedGeneration
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaYonedaInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SiftedColimitPreservation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.PolynomialCategory

public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaRestrictionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.DiscreteComponentLabels
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTensorDesc
public import SerrePositivity.InfinityCategories.HTT.Section6_1_2.OppositeIso
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.DiscreteEmbedding
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# 単体的可換 k 代数（animated 代数）の ∞ 圏 P_Σ(Poly_k) と離散環の埋め込み

## 概要
有限生成多項式 k 代数 k[X_1,…,X_n]（n : ℕ）と k 代数の射の圏 `Poly k` について、その nerve の sifted 余極限による完備化
P_Σ(N(Poly k))（F2 の `SigmaPresheafInfinity`：有限余積を積へ送る空間値前層の ∞ 圏）を単体的可換 k 代数の ∞ 圏とする
（Lurie SAG 25.1.1.1、HTT 5.5.8）。Yoneda j : Poly k → P_Σ は充満忠実で像は compact projective な生成系。離散 k 代数 R は
P ↦ Hom_k(P, R)（有限余積を保つ前層）で埋め込む（HTT 5.5.8.10）。

## 方針
基盤の F2/Presentable の P_Σ をそのまま使う。多項式代数は添字 n : ℕ（a2-design §6 の 3）。離散環の埋め込みは E3 の `algebraNerve k`
（`nerve (Under (CommRingCat.of k))`）からの単体的集合の射として作る（E3 の `perfd` の始域に合わせる）。

## 規約
k = A/d（prism の商）を想定するが、ここでは任意の可換環 k。原典の「導来 p 完備な単体的代数」ではなく P_Σ 全体を始域にする（D32）。
生成系は完備化しない多項式代数（D32）。

## 使われ方
A2-2（Δ の左 Kan 延長、HTT 5.5.8.15）、A2-3（HT filtration）、A3（Lemma 7.7 の「単体的 A/I 代数」）、A4（Def 8.2 の S）、
E3 の `perfd` の始域との接続（`discreteToAnimated`）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories

variable (k : Type u) [CommRing k]

/-! ## 多項式代数の圏 -/

/-! 多項式代数の対象と射は本体の `Prismatic.Poly` を使う。 -/

/-- 概要：多項式代数の有限余積 k[X_n] ⊗ k[X_m] = k[X_{n+m}]。
方針：`MvPolynomial.sumAlgEquiv` と `Fin` の和。
規約：P_Σ の条件（有限余積を積へ）に使う。
使われ方：`IsSigmaPresheaf` の検証。 -/
def polyCoproduct (P Q : Poly k) : Poly k := ⟨P.n + Q.n⟩

def polyCofan (P Q : Poly k) : Limits.BinaryCofan P Q :=
  Limits.BinaryCofan.mk (P := polyCoproduct k P Q)
    (MvPolynomial.rename (Fin.castAdd Q.n)) (MvPolynomial.rename (Fin.natAdd P.n))

def polyCoproduct_isCoproduct (P Q : Poly k) : Limits.IsColimit (polyCofan k P Q) := by
  sorry -- 二つの AlgHom の変数像を Fin.addCases でつなぎ、aeval の一意性を使う

/-- 概要：多項式代数の圏の nerve（小さい形状）。
方針：Mathlib の `nerve`。
規約：SSet.{u}。
使われ方：P_Σ の添字。 -/
abbrev polyNerve : SSet.{u} := nerve (Poly k)

/-! ## animated 代数 -/

/-- 概要：単体的可換 k 代数の ∞ 圏 := P_Σ(N(Poly k))。
方針：F2 の `SigmaPresheafInfinity`。
規約：SSet.{u+1}。quasicategory 性は F2 の instance。
使われ方：Δ の始域。 -/
abbrev AnimatedAlgebra : SSet.{u + 1} := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity (polyNerve k)

/-- 概要：Yoneda j : N(Poly k) → P_Σ（持ち上げた形状から）。
方針：F1 の Yoneda 埋め込み `PresheafInfinity` への射と、表現可能前層が有限余積を積へ送ること（HTT 5.5.8.10、F2 の `SigmaYonedaFiniteCoproducts`）で
`sigmaPresheafInfinityLift`。
規約：充満忠実（F1 の `YonedaInfinityFullyFaithful`）、像は compact projective（HTT 5.5.8.22）。
使われ方：Δ_0 の始域、(1) の主張。
Yoneda の因子化には F2 の `sigmaYonedaInfinityMap` を使う。 -/
def polyYoneda : (SSet.uliftFunctor.{u + 1, u}).obj (polyNerve k) ⟶ AnimatedAlgebra k :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap (polyNerve k)

theorem polyYoneda_fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (polyYoneda k) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap_isFullyFaithful _

theorem polyNerve_finiteCoproducts (J : Type u) [Finite J]
    (D : nerve (Discrete J) ⟶ (polyNerve k).op) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit D := by
  sorry -- 空族は変数 0、二項は polyCofan。有限族の余積錐を opposite の nerve に移す

/-- P_Σ の小 sifted 余極限と、各頂点の多項式による sifted 表示。 -/
theorem animatedAlgebra_siftedColimits :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallSiftedColimits (AnimatedAlgebra k) ∧ ∀ v : (AnimatedAlgebra k) _⦋0⦌,
      ∃ (B : SSet.{u}) (D : B ⟶ polyNerve k)
        (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u+1,u}).map D ≫ polyYoneda k)),
        Quasicategory B ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B ∧ c.vertex = v ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.sigma_hasSmallSiftedColimits _, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheaf_siftedPresentation _ (polyNerve_finiteCoproducts k)⟩

/-- 概要：HTT 5.5.8.15：sifted 余極限をもつ ∞ 圏 𝒱 について、sifted 余極限を保つ関手 P_Σ → 𝒱 の制限 Fun^Σ(P_Σ, 𝒱) → Fun(N(Poly), 𝒱) は同値。
方針：F2 の `SigmaLeftKanAllColimitPreservation`・`SigmaYonedaColimitPreservationCriterion`。
規約：存在（左 Kan 延長）と一意性（sifted 余極限保存な延長は一意）を分けて述べる。
使われ方：A2-2 の `derivedPrismaticCohomology` の定義と性質。 -/
theorem exists_siftedExtension {V : SSet.{u + 1}} [Quasicategory V]
    (hV : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallSiftedColimits V)
    (F : (SSet.uliftFunctor.{u+1,u}).obj (polyNerve k) ⟶ V) :
    ∃ G : AnimatedAlgebra k ⟶ V, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits G ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (polyYoneda k ≫ G) F) := by
  obtain ⟨G, β, hβ, e⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigma_exists_leftKanExtension_with_recovery (polyNerve_finiteCoproducts k) hV F
  exact ⟨G, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLeftKanExtension_preservesSmallSiftedColimits β hβ, e⟩

theorem siftedRestriction_equivalence {V : SSet.{u+1}} [Quasicategory V] (hV : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallSiftedColimits V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaSiftedContinuousRestriction (polyNerve k) V) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaSiftedContinuousRestriction_isQCatEquivalence _ (polyNerve_finiteCoproducts k) V hV

/-- 多項式上の関手を指定された回収同型つきで延長する。 -/
def siftedLan {V : SSet.{u+1}} [Quasicategory V] (hV : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallSiftedColimits V)
    (F : (SSet.uliftFunctor.{u+1,u}).obj (polyNerve k) ⟶ V) := (exists_siftedExtension k hV F).choose

def siftedLanIso {V : SSet.{u+1}} [Quasicategory V] (hV : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallSiftedColimits V)
    (F : (SSet.uliftFunctor.{u+1,u}).obj (polyNerve k) ⟶ V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (polyYoneda k ≫ siftedLan k hV F) F :=
  (exists_siftedExtension k hV F).choose_spec.2.some

/-! ## 離散環の埋め込み -/

/-- 概要：離散 k 代数 R を、集合値前層 P ↦ Hom_k(P, R) として（1 圏の関手）。
方針：`Under (CommRingCat.of k) ⥤ (Poly k)ᵒᵖ ⥤ Type u`。
規約：有限余積を積へ送る（Hom(P ⊗ Q, R) = Hom(P, R) × Hom(Q, R)）。
使われ方：`discreteToAnimated`。 -/
def polyAlgebras : Poly k ⥤ Under (CommRingCat.of k) where
  obj P := BhattScholze.PerfectoidizationInterface.ofAlgebra k (MvPolynomial (Fin P.n) k)
  map f := Under.homMk (CommRingCat.ofHom f.toRingHom) (by ext a; exact f.commutes a)
  map_id := by sorry -- 係数と全変数で恒等
  map_comp := by sorry -- AlgHom の合成

def polyAlgebraNerve : (SSet.uliftFunctor.{u+1,u}).obj (polyNerve k) ⟶ nerve (Under (CommRingCat.of k)) where
  app n := ↾fun x => ((polyAlgebras k).mapComposableArrows _).obj x.down
  naturality := by sorry -- 射列の制限と後合成は可換

def discretePresheaf : Under (CommRingCat.of k) ⥤ ((Poly k)ᵒᵖ ⥤ Type u) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (polyAlgebras k).op

/-- 概要：集合値前層を空間値前層（`PresheafInfinity`）の頂点として読む（離散空間）。
方針：集合値前層の 1 圏の nerve から `PresheafInfinity (polyNerve k)` への射（離散埋め込み）。
規約：—
使われ方：`discreteToAnimated`。
離散 Kan 複体を用いて同時評価の nerve をカリー化する。 -/
def discreteSpaceFunctor : Type u ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj T := ⟨nerve (Discrete T), _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.discreteNerve_kanComplex T⟩
  map f := nerveMap (Discrete.functor (fun t => Discrete.mk (f t)))
  map_id := by sorry -- 離散 nerve のラベルで判定
  map_comp := by sorry -- ラベル写像の合成

def setPresheafEvaluation :
    nerve ((Poly k)ᵒᵖ ⥤ Type u) ⊗ (SSet.uliftFunctor.{u+1,u}).obj (nerve (Poly k)ᵒᵖ) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} where
  app n := ↾fun x => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram
    ((⟨ULift.down, fun _ _ h => h⟩ : ULift.{u} (Fin (n.unop.len + 1)) →o Fin (n.unop.len + 1)).toFunctor ⋙
      (x.2.down.prod' x.1) ⋙ (_root_.CategoryTheory.Functor.uncurry.obj (evaluation (Poly k)ᵒᵖ (Type u))) ⋙ discreteSpaceFunctor)
  naturality := by sorry -- 二つの射列の同時制限は評価の射列の制限

def discretePresheafEmbedding : nerve ((Poly k)ᵒᵖ ⥤ Type u) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity (polyNerve k) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.curryTensorRight ((𝟙 _ ⊗ₘ (SSet.uliftFunctor.{u+1,u}).map (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso (Poly k)).inv) ≫
    setPresheafEvaluation k)

/-- 概要：離散 k 代数の ∞ 圏（E3 の `algebraNerve k`）から animated 代数への埋め込み R ↦ (P ↦ Hom_k(P, R))。
方針：`nerveMap (discretePresheaf k) ≫ discretePresheafEmbedding k` を、有限積保存（`IsSigmaPresheaf`）の検証つきで
`sigmaPresheafInfinityLift` で P_Σ へ。
規約：E3 の `perfd` の始域はこの合成で Δ に接続する。
使われ方：A4（S_perfd の定義域）、E3。 -/
def discreteToAnimated : nerve (Under (CommRingCat.of k)) ⟶ AnimatedAlgebra k :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityLift (nerveMap (discretePresheaf k) ≫ discretePresheafEmbedding k) (by
    sorry) -- Hom(∐ P_i,S) は Hom(P_i,S) の積、空族は一点

/-- 概要：多項式代数 R = k[X_n] の離散埋め込みは Yoneda j(n) に一致。
方針：Hom_k(P, k[X_n]) は表現可能前層。
規約：同値（頂点の同型）で述べる。
使われ方：(1) を離散 R へ移す、A0 の Δ との接続。 -/
theorem discreteToAnimated_poly (n : ℕ) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((discreteToAnimated k).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((polyAlgebras k).obj ⟨n⟩)))
      ((polyYoneda k).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (⟨n⟩ : Poly k))))) := by
  sorry -- P↦Hom(P,k[X₁,…,Xₙ]) は指定された表現可能前層

/-- 概要：離散埋め込みは充満忠実。
方針：Hom_k(k[X_n], R) = R^n の Yoneda 的な議論（P_Σ の射は生成系で決まる）。
規約：—
使われ方：Δ の離散 R での値が R だけで決まること。 -/
theorem discreteToAnimated_fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (discreteToAnimated k) := by
  sorry -- 離散前層間の写像空間は離散。多項式演算を保つラベル写像は k 代数準同型

/-- 0 切り捨ては離散な k 代数への反射、その単位は X→π₀X。 -/
def animatedPiZeroAdjunction : Σ L : AnimatedAlgebra k ⟶ nerve (Under (CommRingCat.of k)),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L (discreteToAnimated k) := by
  sorry -- 各多項式で連結成分を取り、有限積保存な集合値前層を k 代数に戻す

abbrev animatedPiZero := (animatedPiZeroAdjunction k).1
def animatedPiZeroUnit := (animatedPiZeroAdjunction k).2.unitHom

/-- 離散多項式代数の E∞ 実現を sifted 延長する。 -/
def animatedCAlgRealization : AnimatedAlgebra k ⟶ E.CAlg k :=
  siftedLan k (by sorry) -- G12：CAlg(k) は小さい sifted 余極限をもつ
    (polyAlgebraNerve k ≫ E.discrete k)

/-- A4 が離散入力へ制限するときの始域の同定。 -/
def discreteRealizationIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (discreteToAnimated k ≫ animatedCAlgRealization (E := E) k)
      (E.discrete k) := by
  sorry -- 多項式分解の実現。CAlg の sifted 余極限を底の複体で計算すると S[0] に戻り、
        -- 増大写像は S とその準同型に自然

end SerrePositivity.BhattScholze.Prismatic
