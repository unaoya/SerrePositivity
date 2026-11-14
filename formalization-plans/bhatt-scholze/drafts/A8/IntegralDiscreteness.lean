-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralDiscreteness（仮。原典 Thm 10.11 と E3 の欄 integral）
-- 設計書：formalization-plans/bhatt-scholze/a8-design.md §2.4・§3.3、単位 A8-4。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.HomologicalAlgebra.DerivedInfinity.VertexPredicates
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.Stratification
public import SerrePositivity.BhattScholze.IntegralPerfectoidization.Approximation.IntegralApproximation
public import SerrePositivity.BhattScholze.IntegralPerfectoidization.Approximation.IntegralClosureApproximation
public import SerrePositivity.BhattScholze.IntegralPerfectoidization.Approximation.PerfectoidFilteredColimit
public import SerrePositivity.BhattScholze.IntegralPerfectoidization.Completion.IntegralClosureCompletion

public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.BhattScholze.IntegralPerfectoidization.FiniteEtale.FiniteEtalePerfectoid
-- Lemma 10.12 の層別は本体の CommutativeAlgebra/EtaleStratification/Stratification を使う。
-- 本ファイルは drafts/A8/{AlmostConnectivity,AlmostPurityConnectivity}.lean、drafts/A7/{AnimatedPerfectoidization,UniversalProperty}.lean、
-- drafts/A5/{PerfectSiteComparison,WeaklyInitialAndDescent}.lean、drafts/A4/{InterfaceFields,AfterComparison}.lean（`e3Perfd_eq_direct` は AfterComparison。W9-III-14）を import する。

/-!
# 整代数の perfectoid 化の離散性（BS 著者版 Thm 10.11）と E3 の欄 `integral`

## 概要
R perfectoid（完全 prism (A,(d))）、R → S が整写像の p 完備化なら Δ_{S/A,perf} は離散な完全 p 完備 δ-A 代数で、S_perfd は離散な perfectoid 環。
E3 の欄：任意の整 R 代数 S（非完備も）について `IsDiscrete R (e3Perfd S) ∧ IsIntegralPerfectoid (H⁰) p`。

## 方針
filtered 余極限で有限表示有限に帰着（G-A8-9、perfd は filtered 余極限と可換、perfectoid の p 完備化した余極限は perfectoid G-A8-8）、Cor 8.14 で連結性に帰着、
Lemma 10.12 の層別の長さ n で帰納：n = 1 は S_red が有限エタールで perfectoid（G-A8-6）、Perfd_{S/} = Perfd_{S_red/}（D64）；n > 1 は Prop 8.13 と帰納法の仮定で
(S/g_1)_perfd 連結、Lemma 10.5 で g_1-almost 連結性に帰着し、整閉包 T の**完備化 T̂ = completionRing T** と Cor 8.12（W9-III-04：生の T は導来 p 完備とは
限らない）、T への写像を備えた有限表示有限 A_λ の filtered 系（W9-III-06）に Thm 10.9 の連結性（A8-2）、filtered 余極限。

## 規約
S 離散。E3 の欄は S^∧ 経由（D41）。

## 使われ方
`PerfectoidizationInterfaceCAlg.integral`（A9）。環の帰結は既存（`Perfectoidization/Derived/IntegralExistence`）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial TensorProduct
attribute [local instance] HasDerivedCategory.standard

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

-- 本体で局所的に使う代数構造を、このdraftでも局所的に登録する。
attribute [local instance] reducedAwayBase

open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]

open SerrePositivity.BhattScholze.Almost SerrePositivity.BhattScholze.Prismatic
open SerrePositivity.CommutativeAlgebra SerrePositivity.DerivedCompletion

/-- Lemma 10.12 の三条件。各層は商の被約化を局所化した StratumRing。 -/
def IsEtaleStratification {n : ℕ} (g : Fin n → R) : Prop :=
  Ideal.span (Set.range g) = ⊤ ∧ ∀ i : Fin n,
    let I := earlierIdeal g i
    HasEtaleFactorization p (stratumMap (algebraMap R S) I (g i)) ∧
      ((p : StratumRing I (g i)) = 0 ∨ IsUnit (p : StratumRing I (g i)))

abbrev completedInput (U : A_R R) :=
  (animatedCompletion p R).app _ ((discreteToAnimated R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U))

abbrev completedPerfd (U : A_R R) :=
  (perfectoidizationAnimated (E := E) p R hR).app _ (completedInput p R U)

/-- 概要：D64：perfectoid 環は被約なので Perfd_{S/} = Perfd_{S_red/}、よって S_perfd ≃ (S_red)_perfd（Prop 8.5 の極限の形）。
方針：A5-1 `perfectoidization_isLimit_u` と添字圏の同一視。
規約：—
使われ方：n = 1。 -/
theorem perfectoidization_red :
    let q : ofAlgebra R S ⟶ ofAlgebra R (S ⧸ nilradical S) :=
      Under.homMk (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical S))) rfl
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (((nerve.edgeMk q).map (perfectoidizationFunctor (E := E) p R hR)).toTruncated) := by
  sorry -- perfectoid 標的は被約。商写像が誘導する Perfd の添字圏の同値と A5 の極限

/-- 完備 animated 入力の Δ_perf の離散性と、その H⁰ 上の完全 prism。 -/
def IsDiscretePerfectPerfection (U : A_R R) : Prop :=
    let X := (prismaticPerfectionAnimated (E := E) p R hR).app _ (completedInput p R U)
    let A := perfectPrismRing p R
    let C := cAlgH0Algebra (E := E) A X
    IsTheoryDiscrete (E := E) A X ∧ ∃ Q : OrientedPrism p C.right,
      Q.generator = C.hom.hom (perfectPrism p R hR).generator ∧ Q.deltaStructure.IsPerfect ∧
        (perfectPrism p R hR).deltaStructure.IsDeltaHom Q.deltaStructure C.hom.hom ∧
        Function.Injective (fun x : C.right => (p : C.right) * x) ∧
        IsAdicComplete (Ideal.span {(p : C.right)}) C.right

/-- 概要：有限表示有限 S で S_perfd 連結 ⇒ 整 S（p 完備化）で S_perfd 離散・perfectoid、Δ_perf 離散・完全 δ 環。
方針：Cor 8.14（A7-2）、A5-4 `prismaticPerfection_filteredColimit`、上の二つ。
規約：—
使われ方：Thm 10.11。 -/
theorem perfectoidization_discrete_of_finitePresentation_connective
    (hfin : ∀ U : A_R R, FinitePresentedFinite R U → SerrePositivity.DerivedInfinity.IsConnectiveAt R 0 (perfdModule (E := E) p R hR U))
    (h : Algebra.IsIntegral R S) :
    IsTheoryDiscrete (E := E) R (completedPerfd (E := E) p R hR (ofAlgebra R S)) ∧
      IsIntegralPerfectoid (cAlgH0Algebra (E := E) R (completedPerfd (E := E) p R hR (ofAlgebra R S))).right p ∧
      IsDiscretePerfectPerfection (E := E) p R hR (ofAlgebra R S) := by
  sorry -- 有限表示有限で Lemma 8.4 と Cor 8.14。G-A8-9 の余極限に A4 の保存と G-A8-8 を適用

/-- 概要：n = 1：R → S_red 有限エタール（Lemma 10.12 (2) の普遍同相が同型：p = 0 なら R 完全（perfectoid・被約・Frobenius 全射）で G-A8-5、p 可逆なら構成）
⇒ S_red perfectoid（G-A8-6）⇒ S_perfd ≃ (S_red)_perfd = S_red 離散。
方針：`perfectoidization_red`、`perfectoidization_of_perfectoid`（A7-2）。 -/
theorem perfectoidization_connective_of_stratification_one [Module.Finite R S] [Algebra.FinitePresentation R S]
    (g : Fin 1 → R) (hg : IsEtaleStratification p R S g) :
    SerrePositivity.DerivedInfinity.IsConnectiveAt R 0 (perfdModule (E := E) p R hR (ofAlgebra R S)) := by
  sorry -- g₁ は単元。p=0 では完全被約な層の普遍同相、p 可逆では p 反転後の同型。
        -- S_red は有限エタールで perfectoid、perfectoidization_red とその単位同型

/-- 離散な R 代数 U,V の完備 animated 押し出し。非完備な元も反射単位を経由する。 -/
def quotientTensorInput (U V : A_R R) : (CompleteAnimatedAlgebra p R) _⦋0⦌ := by
  let R₀ : A_R R := Under.mk (𝟙 (CommRingCat.of R))
  let leg (W : A_R R) : R₀ ⟶ W := Under.homMk W.hom (by simp [R₀])
  let F := discreteToAnimated R ≫ animatedCompletion p R
  let D := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan (((nerve.edgeMk (leg U)).map F).toTruncated) (((nerve.edgeMk (leg V)).map F).toTruncated)
  exact (completeAnimatedPushout p R D).1.vertex

abbrev tensorPerfdModule (U V : A_R R) :=
  (perfectoidizationAnimated (E := E) p R hR ≫ E.forget R).app _ (quotientTensorInput p R U V)

/-- 同じ Q_perfd から π₀(Q) の perfd と、両因子の perfd の完備テンソルへ比較する。
R₁ を第二因子とすると π₀ は通常の S⊗_R R₁。 -/
theorem quotientTensor_comparisons [Module.Finite R S] [Algebra.FinitePresentation R S] (g : R) :
    let J := Ideal.span {g}
    let B := QuotientPerfectoidization R J p hR
    let M := perfdModule (E := E) p R hR (ofAlgebra R S)
    let Q := tensorPerfdModule (E := E) p R hR (ofAlgebra R S) (ofAlgebra R (R ⧸ J))
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso Q (perfdModule (E := E) p R hR (ofAlgebra R (S ⧸ Ideal.span {algebraMap R S g})))) ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso Q (quotientTensor (R := R) p hR J M)) ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (tensorPerfdModule (E := E) p R hR (ofAlgebra R S) (ofAlgebra R B))
        (perfdModule (E := E) p R hR (ofAlgebra R (S ⊗[R] B)))) := by
  sorry -- Q の π₀=S/gS と Prop 8.5 系4、Prop 8.13 と (R/g)_perfd=B。
        -- B との完備テンソルも π₀=S⊗_R B（有限表示有限で完備）を経る

/-- 概要：帰納の段：R_1 := (R/g_1)_perfd（perfectoid、Thm 7.4 で R/g_1 の商）、帰納法の仮定を R_1 → S ⊗_R R_1 に当てて (S ⊗̂_R R_1)_perfd 連結。
perfd の接続は二段（W9-III-03 と同じ）：Q := S ⊗̂^L_R R/g_1 は π_0 Q = S/g_1（有限表示加群なので完備）、Prop 8.5 系 4（`perfectoidization_piZero`）で
Q_perfd ≃ (S/g_1)_perfd、Prop 8.13 で Q_perfd ≃ S_perfd ⊗̂_R R_1；同様に S ⊗̂^L_R R_1 の π_0 = S ⊗_R R_1。離散商と導来テンソルを同一視しない。
層別の条件の底変換（紙 3、W9 で ○）：先に底変換し最後に被約化、p 反転後は同型条件が保たれる。
方針：A7-1 `perfectoidization_relativeTensor`、A5-1 `perfectoidization_piZero`。 -/
theorem perfectoidization_quotient_connective_of_ih [Module.Finite R S] [Algebra.FinitePresentation R S]
    {n : ℕ} (g : Fin (n+1) → R) (hg : IsEtaleStratification p R S g)
    (ih : ∀ (R₁ S₁ : Type u) [CommRing R₁] [CommRing S₁] [Algebra R₁ S₁]
      [Module.Finite R₁ S₁] [Algebra.FinitePresentation R₁ S₁] (h₁ : IsIntegralPerfectoid R₁ p)
      (t : Fin n → R₁), IsEtaleStratification p R₁ S₁ t →
        SerrePositivity.DerivedInfinity.IsConnectiveAt R₁ 0 (perfdModule (E := E) p R₁ h₁ (ofAlgebra R₁ S₁))) :
    let J := Ideal.span {g 0}
    let M := perfdModule (E := E) p R hR (ofAlgebra R S)
    let N := perfdModule (E := E) p R hR (ofAlgebra R (S ⧸ Ideal.span {algebraMap R S (g 0)}))
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (quotientTensor (R := R) p hR J M) N) ∧ SerrePositivity.DerivedInfinity.IsConnectiveAt R 0 N := by
  sorry -- Q=S⊗̂^L_R R/g₁、π₀Q=S/g₁。系4と Prop 8.13 を順に適用。
        -- R₁=(R/g₁)_perfd との完備テンソルにも同じ二段を用い、S⊗_R R₁ に残り n 層の ih。
        -- 各層は底変換してから被約化し、p 反転後の同型も移す


/-- 概要：**T は導来 p 完備とは限らない（W9-III-04、致命・修復済み）**。反例：V = ℤ_p[p^{1/p^∞}]^∧、R = V 値の p 進収束列の環（perfectoid、[BMS18, Lemma 3.10 (ii)]）、
g = (p^n)、S = R、T = R の R[1/g] での整閉包。b^(k) = (n mod p^k) ∈ T（有限個の値）は T の p 進 Cauchy 列で、極限 b = (n) は R 上整でない
（部分列 n_ℓ = m + p^ℓ で P_∞ が全ての正整数を零点にもつ）。T ⊂ ∏V で座標射は p 進連続なので T に極限はない。よって T は古典的にも導来的にも p 完備でない。
方針：記録（反例）。生の T の完備性を一般補題にしてはならない。
規約：—
使われ方：設計の根拠。 -/
theorem integralClosure_not_complete_counterexample :
    ∃ (A : CommRingCat.{u}) (_ : IsIntegralPerfectoid A p) (g : A),
      ¬ IsModuleComplete A (p : A) (ModuleCat.of A (integralClosureInLocalization A A g)) := by
  sorry -- A は V 値収束列、g=(p^n)。T の Cauchy 列 (n mod p^k) の極限 (n) は整でない

include hR in
/-- 概要：Cor 8.12（A6-4）を **S → T̂** に当てる：S・g_1S は完備（有限表示有限、乗法写像の像）、T̂ は完備（上）、ArcOutside（上）。
fib(S_perfd → T̂_perfd) ≃ fib((S/g_1)_perfd → (T̂/g_1T̂)_perfd) は (R/g_1)_perfd 加群なので S_perfd → T̂_perfd = e3Perfd(T)（D41）は g_1-almost 同型。
商 T̂/g_1T̂ を含む比較は A6 §2.3 の自然同型 F_U ≃ F_{completionRing U}（`homPresheaf_completionRing_iso`）で。
方針：`perfectoidization_excision`、A8-2 `perfectoidization_almostIso_of_localization_iso` と同じ fibre の係数の議論。
規約：原典の暗黙の完備化を明示（D70）。Thm 10.11 の結論・E3 の引用は使わない。
使われ方：`perfectoidization_almostConnective_of_stratification`。 -/
theorem perfectoidization_almostIso_integralClosureCompletion [Module.Finite R S] [Algebra.FinitePresentation R S]
    (g : R) (h : Algebra.IsIntegral R S) (het : FiniteEtaleAway R (S ⧸ nilradical S) g) :
    IsJAlmostZero p R hR (Ideal.span {g}) (perfdMapFiber (E := E) p R hR (completedClosureArrow p R S g h)) := by
  sorry -- S、T̂、gS の完備性と arcOutside_completionRing で Cor 8.12。商の fibre は (R/g)_perfd 加群

/-- 概要：g_1-almost 連結性：S_perfd → T̂_perfd は g_1-almost 同型（上）、T̂_perfd は g_1-almost 連結：各 A_λ に Thm 10.9 の連結性（A8-2、A_λ[1/g_1] = B は
R[1/g_1] 上有限エタール）、A5 の filtered 余極限保存を完備圏で使って T̂_perfd ≃ LΛ_p(colim_λ (A_λ)_perfd)、A8-1 の
`isAlmostConnective_completedFilteredColimit`（almost 連結な完備複体は完備 filtered 余極限で閉じる）で T̂_perfd は g_1-almost 連結。
G-A8-8 はここでは使わない（(A_λ)_perfd が perfectoid とはまだ分からない。使えば Thm 10.11 の先取り、W9-III-10）。
方針：A8-2 `perfectoidization_almostConnective_of_finiteEtaleAway`、`perfectoidization_almostIso_integralClosureCompletion`、
`exists_finitePresentation_approximation_fixedLocalization`、A8-1 `isAlmostConnective_completedFilteredColimit`（Codex 第 3 部続き 2 で全接続 ○）。 -/
theorem perfectoidization_almostConnective_of_stratification [Module.Finite R S] [Algebra.FinitePresentation R S]
    {n : ℕ} (g : Fin (n+1) → R) (hg : IsEtaleStratification p R S g) :
    IsAlmostConnective p R hR (Ideal.span {g 0}) (perfdModule (E := E) p R hR (ofAlgebra R S)) := by
  sorry -- A_λ[1/g₁]≃B に Thm 10.9、G-A8-1 の完備 filtered 余極限の系で T̂_perfd へ。
        -- S→T̂ の almost 同型で戻す。各 A_λ の離散性・perfectoid 性は仮定しない

/-- 概要：Thm 10.11 の連結性：有限表示有限 S で S_perfd 連結（Lemma 10.12 の層別の長さの帰納、Lemma 10.5 で合わせる）。
方針：`exists_finiteEtaleStratification`（A8-3）、上の三つ、A8-1 `connective_iff_almost`。 -/
theorem perfectoidization_connective_of_finitePresentation [Module.Finite R S] [Algebra.FinitePresentation R S]
    (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    SerrePositivity.DerivedInfinity.IsConnectiveAt R 0 (perfdModule (E := E) p R hR (ofAlgebra R S)) := by
  obtain ⟨n, g, hspan, hstrata⟩ := exists_finiteEtaleStratification (R := R) (S := S) p hZp
  sorry -- 長さで帰納。空列なら R は零環、1 層は G-A8-6。帰納段の二条件を Lemma 10.5 で合わせる

/-- 概要：Thm 10.11：S = (整 R 代数)^∧ で Δ_{S/A,perf} は離散な完全 p 完備 δ-A 代数、S_perfd は離散な perfectoid 環。
方針：上の二つ。
規約：原典の形（D67）。
使われ方：`e3Integral`。 -/
theorem prismaticPerfection_discrete_of_integral (h : Algebra.IsIntegral R S) :
    IsDiscretePerfectPerfection (E := E) p R hR (ofAlgebra R S) := by
  sorry -- 有限表示有限の連結性、G-A8-9・8、d 進 Nakayama と A4 の完全 δ 構造

theorem perfectoidization_isIntegralPerfectoid_of_integral (h : Algebra.IsIntegral R S) :
    let x := completedPerfd (E := E) p R hR (ofAlgebra R S)
    IsTheoryDiscrete (E := E) R x ∧ IsIntegralPerfectoid (cAlgH0Algebra (E := E) R x).right p := by
  sorry -- p 完備 perfectoid 基底では p 以外の素数は単元。hZp を供給して有限表示有限の
        -- 連結性を perfectoidization_discrete_of_finitePresentation_connective に渡す

/-- 概要：E3 の `integral`：任意の整 R 代数 S（非完備も）について `IsDiscrete R (e3Perfd S) ∧ IsIntegralPerfectoid (H⁰(e3Perfd S)) p`。
方針：`e3Perfd S = (S^∧)_perfd`（D41、S^∧ = completionRing S = π_0(LΛ_p S)）。Thm 10.11 は原典どおり animated LΛ_p S（整写像の導来 p 完備化）について示し、
Prop 8.5 の系 4（`perfectoidization_piZero`、決定 6）で (LΛ_p S)_perfd ≃ (S^∧)_perfd、`e3H0_of_complete`（A4-3）。
規約：`PerfectoidizationInterfaceCAlg.integral` の型そのまま。
使われ方：A9。 -/
theorem e3Integral (hR : IsIntegralPerfectoid R p := by assumption) (S : A_R R)
    (h : letI : Algebra R S.right := S.hom.hom.toAlgebra; Algebra.IsIntegral R S.right) :
    IsTheoryDiscrete (E := E) R ((e3Perfd (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S)) ∧
      IsIntegralPerfectoid ((e3H0RingData (E := E) p R hR).ringFunctor.obj S).right p := by
  sorry -- Thm 10.11 の入力は animated な LΛ_p S。Prop 8.5 系4でその perfd を
        -- π₀(LΛ_p S)=completionRing p S.right の perfd に移し、A4 の完備入力比較で欄を読む

end SerrePositivity.BhattScholze.Perfectoidization.Derived
