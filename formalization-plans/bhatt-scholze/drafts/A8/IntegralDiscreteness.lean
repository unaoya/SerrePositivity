-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralDiscreteness（仮。原典 Thm 10.11 と E3 の欄 integral）
-- 設計書：formalization-plans/bhatt-scholze/a8-design.md §2.4・§3.3、単位 A8-4。基準コミット 972bb7f53。ビルドしない。
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import SerrePositivity.EInfinity.Perfectoidization.Interface
public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
-- 本ファイルは drafts/A8/{AlmostConnectivity,AlmostPurityConnectivity,Stratification}.lean、drafts/A7/{AnimatedPerfectoidization,UniversalProperty}.lean、
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

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]

open SerrePositivity.BhattScholze.Almost SerrePositivity.BhattScholze.Prismatic
open SerrePositivity.CommutativeAlgebra SerrePositivity.DerivedCompletion
open SerrePositivity.EInfinity.BarrattEccles

def FinitePresentedFinite (U : A_R R) : Prop :=
  letI := U.hom.hom.toAlgebra
  Module.Finite R U.right ∧ Algebra.FinitePresentation R U.right

/-- Lemma 10.12 の三条件。各層は商の被約化を局所化した StratumRing。 -/
def IsEtaleStratification {n : ℕ} (g : Fin n → R) : Prop :=
  Ideal.span (Set.range g) = ⊤ ∧ ∀ i : Fin n,
    let I := earlierIdeal g i
    HasEtaleFactorization p (stratumMap (algebraMap R S) I (g i)) ∧
      ((p : StratumRing I (g i)) = 0 ∨ IsUnit (p : StratumRing I (g i)))

abbrev completedInput (U : A_R R) :=
  (animatedCompletion p R).app _ ((discreteToAnimated R).app _ (nerveVertex U))

abbrev completedPerfd (U : A_R R) :=
  (perfectoidizationAnimated p R hR).app _ (completedInput p R U)

/-- 概要：G-A8-6：perfectoid R 上の有限エタール代数 T は perfectoid。
方針：T は p 完備（有限射影）、T/p は R/p 上エタールで相対 Frobenius が同型なので φ_T 全射、W(T^♭) は W(R^♭) のエタール持ち上げで ker θ_T = d·W(T^♭)。
規約：`IsIntegralPerfectoid`。
使われ方：n = 1。 -/
include hR in
theorem isIntegralPerfectoid_of_finiteEtale (T : Type u) [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T] :
    IsIntegralPerfectoid T p := by sorry -- 有限射影なので導来 p 完備。相対 Frobenius とエタール持ち上げで Fontaine 核を移す

/-- 概要：D64：perfectoid 環は被約なので Perfd_{S/} = Perfd_{S_red/}、よって S_perfd ≃ (S_red)_perfd（Prop 8.5 の極限の形）。
方針：A5-1 `perfectoidization_isLimit_u` と添字圏の同一視。
規約：—
使われ方：n = 1。 -/
theorem perfectoidization_red :
    let q : ofAlgebra R S ⟶ ofAlgebra R (S ⧸ nilradical S) :=
      Under.homMk (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical S))) rfl
    IsInvertibleEdge (((nerve.edgeMk q).map (perfectoidizationFunctor p R hR)).toTruncated) := by
  sorry -- perfectoid 標的は被約。商写像が誘導する Perfd の添字圏の同値と A5 の極限

/-- 概要：G-A8-9：整 R 代数は有限表示有限 R 代数の filtered 余極限（R[x]/I を I の有限生成部分イデアル（モニック関係を含む）で近似）。 -/
theorem integral_isFilteredColimit_finitePresentation (h : Algebra.IsIntegral R S) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I) (F : I ⥤ A_R R)
      (η : F ⟶ (Functor.const I).obj (ofAlgebra R S)),
      (∀ i, FinitePresentedFinite R (F.obj i)) ∧ Nonempty (IsColimit (Cocone.mk _ η)) := by
  sorry -- 有限個の整元のモニック関係を含む有限表示と有限個の関係を動かす

/-- 概要：G-A8-8：perfectoid 環の p 完備化した filtered 余極限は perfectoid で、p^∞ ねじれが p で殺される（Lemma 2.34 (2)）ので導来 p 完備化は離散。
方針（Codex W9 第 3 部続き 2 で ○）：共通基底（cofinal な λ₀/）の完全 prism (B_λ, d)（同じ d、Thm 3.10 と剛性）、C = colim B_λ は完全 δ 環で p・d 非零因子、
C/d = P。p 完備化（p ねじれなしで離散、φ^{-1} は p 進連続）、mod d の cofiber は完備化と可換で LΛ_p P = P̂ 離散、d は完備化後も非零因子；d 完備化
（Lemma 3.9 の順序）で離散な (p,d) 完備 D、D/d = P̂、D は完全 δ 環、(D,(d)) 完全 prism、Thm 3.10。W が任意の filtered 余極限と可換とは言わない。
規約：**使う場所は一般の整代数への帰着（有限表示有限の連結性と Cor 8.14 の後）だけ**。A_λ の段では使わない（W9-III-10、`isAlmostConnective_completedFilteredColimit`）。
使われ方：filtered 余極限での帰着。 -/
theorem isIntegralPerfectoid_completedFilteredColimit {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i, IsIntegralPerfectoid (F.obj i) p) :
    IsIntegralPerfectoid (completionRing p c.pt) p ∧
      (∀ (x : c.pt) (n : ℕ), (p : c.pt)^n * x = 0 → (p : c.pt) * x = 0) ∧
      (∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat c.pt) i).obj
        ((derivedComplexCompletionFunctor c.pt (p : c.pt)).obj
          ((moduleObjectFunctor c.pt).obj (ModuleCat.of c.pt c.pt))))) := by
  sorry -- 完全 prism の余極限を p 完備化し、その後で d 完備化。mod d は LΛ_p(colim F)。
        -- 有界 p 冪ねじれによりこの導来完備化は離散

/-- 完備 animated 入力の Δ_perf の離散性と、その H⁰ 上の完全 prism。 -/
def IsDiscretePerfectPerfection (U : A_R R) : Prop :=
    let X := (prismaticPerfectionAnimated p R hR).app _ (completedInput p R U)
    let A := perfectPrismRing p R
    let C := cAlgH0Algebra A X
    IsDiscrete A X ∧ ∃ Q : OrientedPrism p C.right,
      Q.generator = C.hom.hom (perfectPrism p R hR).generator ∧ Q.deltaStructure.IsPerfect ∧
        (perfectPrism p R hR).deltaStructure.IsDeltaHom Q.deltaStructure C.hom.hom ∧
        Function.Injective (fun x : C.right => (p : C.right) * x) ∧
        IsAdicComplete (Ideal.span {(p : C.right)}) C.right

/-- 概要：有限表示有限 S で S_perfd 連結 ⇒ 整 S（p 完備化）で S_perfd 離散・perfectoid、Δ_perf 離散・完全 δ 環。
方針：Cor 8.14（A7-2）、A5-4 `prismaticPerfection_filteredColimit`、上の二つ。
規約：—
使われ方：Thm 10.11。 -/
theorem perfectoidization_discrete_of_finitePresentation_connective
    (hfin : ∀ U : A_R R, FinitePresentedFinite R U → Derived.IsConnectiveAt R 0 (perfdModule p R hR U))
    (h : Algebra.IsIntegral R S) :
    IsDiscrete R (completedPerfd p R hR (ofAlgebra R S)) ∧
      IsIntegralPerfectoid (cAlgH0Algebra R (completedPerfd p R hR (ofAlgebra R S))).right p ∧
      IsDiscretePerfectPerfection p R hR (ofAlgebra R S) := by
  sorry -- 有限表示有限で Lemma 8.4 と Cor 8.14。G-A8-9 の余極限に A4 の保存と G-A8-8 を適用

/-- 概要：n = 1：R → S_red 有限エタール（Lemma 10.12 (2) の普遍同相が同型：p = 0 なら R 完全（perfectoid・被約・Frobenius 全射）で G-A8-5、p 可逆なら構成）
⇒ S_red perfectoid（G-A8-6）⇒ S_perfd ≃ (S_red)_perfd = S_red 離散。
方針：`perfectoidization_red`、`perfectoidization_of_perfectoid`（A7-2）。 -/
theorem perfectoidization_connective_of_stratification_one [Module.Finite R S] [Algebra.FinitePresentation R S]
    (g : Fin 1 → R) (hg : IsEtaleStratification p R S g) :
    Derived.IsConnectiveAt R 0 (perfdModule p R hR (ofAlgebra R S)) := by
  sorry -- g₁ は単元。p=0 では完全被約な層の普遍同相、p 可逆では p 反転後の同型。
        -- S_red は有限エタールで perfectoid、perfectoidization_red とその単位同型

/-- 離散な R 代数 U,V の完備 animated 押し出し。非完備な元も反射単位を経由する。 -/
def quotientTensorInput (U V : A_R R) : (CompleteAnimatedAlgebra p R) _⦋0⦌ := by
  let R₀ : A_R R := Under.mk (𝟙 (CommRingCat.of R))
  let leg (W : A_R R) : R₀ ⟶ W := Under.homMk W.hom (by simp [R₀])
  let F := discreteToAnimated R ≫ animatedCompletion p R
  let D := edgeSpan (((nerve.edgeMk (leg U)).map F).toTruncated) (((nerve.edgeMk (leg V)).map F).toTruncated)
  exact (completeAnimatedPushout p R D).1.vertex

abbrev tensorPerfdModule (U V : A_R R) :=
  (perfectoidizationAnimated p R hR ≫ cAlgForgetDerived R).app _ (quotientTensorInput p R U V)

/-- 同じ Q_perfd から π₀(Q) の perfd と、両因子の perfd の完備テンソルへ比較する。
R₁ を第二因子とすると π₀ は通常の S⊗_R R₁。 -/
theorem quotientTensor_comparisons [Module.Finite R S] [Algebra.FinitePresentation R S] (g : R) :
    let J := Ideal.span {g}
    let B := QuotientPerfectoidization R J p hR
    let M := perfdModule p R hR (ofAlgebra R S)
    let Q := tensorPerfdModule p R hR (ofAlgebra R S) (ofAlgebra R (R ⧸ J))
    Nonempty (VertexIso Q (perfdModule p R hR (ofAlgebra R (S ⧸ Ideal.span {algebraMap R S g})))) ∧
      Nonempty (VertexIso Q (quotientTensor p R hR J M)) ∧
      Nonempty (VertexIso (tensorPerfdModule p R hR (ofAlgebra R S) (ofAlgebra R B))
        (perfdModule p R hR (ofAlgebra R (S ⊗[R] B)))) := by
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
        Derived.IsConnectiveAt R₁ 0 (perfdModule p R₁ h₁ (ofAlgebra R₁ S₁))) :
    let J := Ideal.span {g 0}
    let M := perfdModule p R hR (ofAlgebra R S)
    let N := perfdModule p R hR (ofAlgebra R (S ⧸ Ideal.span {algebraMap R S (g 0)}))
    Nonempty (VertexIso (quotientTensor p R hR J M) N) ∧ Derived.IsConnectiveAt R 0 N := by
  sorry -- Q=S⊗̂^L_R R/g₁、π₀Q=S/g₁。系4と Prop 8.13 を順に適用。
        -- R₁=(R/g₁)_perfd との完備テンソルにも同じ二段を用い、S⊗_R R₁ に残り n 層の ih。
        -- 各層は底変換してから被約化し、p 反転後の同型も移す

/-! ## g_1-almost 連結性（W9-III-04〜06 で修復）：整閉包 T、その完備化 T̂、局所化を固定した近似 -/

/-- 概要：B := S_red[1/g_1]（R[1/g_1] 上有限エタール、Lemma 10.12 (2)）、T := R の B における代数的整閉包（原典の S′）。S → S_red → T ⊂ B で **S → T は整**
（T の元を零化する R 係数のモニック式は S 係数でもある）。T ⊂ B であって B ⊂ T ではない。
方針：Mathlib `integralClosure`。
規約：S → T の局所化は同型とは限らない（W9-III-05：S = V[ε]/(ε²)、g_1 = p で S[1/p] に ε が残る。原典が述べるのは arc 層の同型）。
使われ方：以下。 -/
abbrev reducedAway (g : R) := Localization.Away (algebraMap R (S ⧸ nilradical S) g)

local instance reducedAwayBase (g : R) : Algebra R (reducedAway R S g) :=
  ((algebraMap (S ⧸ nilradical S) (reducedAway R S g)).comp (algebraMap R (S ⧸ nilradical S))).toAlgebra

def integralClosureInLocalization (g : R) : Subalgebra R (reducedAway R S g) :=
  integralClosure R (reducedAway R S g)

def toIntegralClosure (g : R) (h : Algebra.IsIntegral R S) :
    S →ₐ[R] integralClosureInLocalization R S g := by
  let f : S →ₐ[R] reducedAway R S g := {
    __ := (algebraMap (S ⧸ nilradical S) _).comp (Ideal.Quotient.mk (nilradical S))
    commutes' := by intro r; rfl }
  exact f.codRestrict _ (fun x => IsIntegral.map f (h.isIntegral x))

def closureArrow (g : R) (h : Algebra.IsIntegral R S) :
    ofAlgebra R S ⟶ ofAlgebra R (integralClosureInLocalization R S g) :=
  Under.homMk (CommRingCat.ofHom (toIntegralClosure R S g h).toRingHom) (by ext; simp)

theorem integralClosureInLocalization_integral (g : R) (h : Algebra.IsIntegral R S) :
    (toIntegralClosure R S g h).toRingHom.IsIntegral := by
  sorry -- 元を零化する R 係数のモニック式を S に移す

/-- 概要：S → T は `ArcOutside`（g_1 を殺さない p 完備な階数 1 の付値環 W への射は T へ一意に延びる）。
方針：W は被約なので S → W は S_red を通り、局所化で B → Frac(W)、T に制限、T の整性と W の整閉性で像は W に入る。一意性は T[1/g_1] = B と W ⊂ Frac(W)。
G-A8-3″ を S に直接は当てない（局所化は同型でない）。
規約：界面の `ArcOutside`。
使われ方：`arcOutside_completionRing`。 -/
theorem integralClosureInLocalization_arcOutside (g : R) (h : Algebra.IsIntegral R S) :
    ArcOutside R p (closureArrow R S g h) (Ideal.span {algebraMap R S g}) := by
  sorry -- W は被約、S_red[1/g]→Frac(W) を T に制限。整閉性で W に入り、T[1/g]=B で一意

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

/-- 概要：G-A8-10：T の p 冪ねじれは有界（B は R[1/g_1] 上有限エタールで平坦、perfectoid R の p 冪ねじれは p で殺される（Lemma 2.34 (2)）、部分環 T も）。
よって T の導来 p 完備化は離散で、古典的 p 完備化 T̂ := completionRing T に一致する。
方針：既存の `completionRing`（H⁰(LΛ_p)）と有界ねじれでの離散性（DerivedGeneral/Truncation）。
規約：—
使われ方：Cor 8.12 の前提（T̂ は離散で導来 p 完備）。 -/
def integralClosureCompletion (g : R) : A_R R :=
  (PerfectoidizationInterface.completionFunctor p R).obj (ofAlgebra R (integralClosureInLocalization R S g))

def completedClosureArrow (g : R) (h : Algebra.IsIntegral R S) :
    ofAlgebra R S ⟶ integralClosureCompletion p R S g :=
  closureArrow R S g h ≫ (completionAlgebraUnit p R).app _

include hR in
theorem integralClosureCompletion_isModuleComplete (g : R) (het : FiniteEtaleAway R (S ⧸ nilradical S) g) :
    let T := integralClosureInLocalization R S g
    let C := (integralClosureCompletion p R S g).right
    let I := Ideal.span {(p : T)}
    IsModuleComplete C (p : C) (ModuleCat.of C C) ∧
      (∃ e : C ≃+* AdicCompletion I T,
        e.toRingHom.comp (completionUnit p (CommRingCat.of T)).hom = algebraMap T (AdicCompletion I T)) ∧
      ∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat T) i).obj
        ((derivedComplexCompletionFunctor T (p : T)).obj ((moduleObjectFunctor T).obj (ModuleCat.of T T)))) := by
  sorry -- B は R[1/g] に平坦、部分環 T の p^∞ ねじれは p で消える。LΛ_p T は離散で H⁰=T̂

/-- 概要：S → T̂ も `ArcOutside`：W は p 完備なので T → W は T̂ → W に一意に延びる（`completion_existsUnique`）。T̂/S の整性は要らない。
方針：`integralClosureInLocalization_arcOutside` と `completionRing` の普遍性。
規約：—
使われ方：Cor 8.12 の適用。 -/
theorem arcOutside_completionRing (g : R) (h : Algebra.IsIntegral R S) :
    ArcOutside R p (completedClosureArrow p R S g h) (Ideal.span {algebraMap R S g}) := by
  sorry -- S→T の一意延長に completion_existsUnique を適用。T̂/S の整性は使わない

/-- 概要：Cor 8.12（A6-4）を **S → T̂** に当てる：S・g_1S は完備（有限表示有限、乗法写像の像）、T̂ は完備（上）、ArcOutside（上）。
fib(S_perfd → T̂_perfd) ≃ fib((S/g_1)_perfd → (T̂/g_1T̂)_perfd) は (R/g_1)_perfd 加群なので S_perfd → T̂_perfd = e3Perfd(T)（D41）は g_1-almost 同型。
商 T̂/g_1T̂ を含む比較は A6 §2.3 の自然同型 F_U ≃ F_{completionRing U}（`homPresheaf_completionRing_iso`）で。
方針：`perfectoidization_excision`、A8-2 `perfectoidization_almostIso_of_localization_iso` と同じ fibre の係数の議論。
規約：原典の暗黙の完備化を明示（D70）。Thm 10.11 の結論・E3 の引用は使わない。
使われ方：`perfectoidization_almostConnective_of_stratification`。 -/
theorem perfectoidization_almostIso_integralClosureCompletion [Module.Finite R S] [Algebra.FinitePresentation R S]
    (g : R) (h : Algebra.IsIntegral R S) (het : FiniteEtaleAway R (S ⧸ nilradical S) g) :
    IsJAlmostZero p R hR (Ideal.span {g}) (perfdMapFiber p R hR (completedClosureArrow p R S g h)) := by
  sorry -- S、T̂、gS の完備性と arcOutside_completionRing で Cor 8.12。商の fibre は (R/g)_perfd 加群

/-- 概要：G-A8-11（W9-III-06）：T への写像を備えた有限表示有限 R 代数 A_λ の filtered 系で、各 A_λ[1/g_1] ≅ B（R[1/g_1] 代数として）、colim A_λ = T。
方針：B は R[1/g_1] 上有限エタールなので有限表示；生成元の分母を払って T 内に取り、モニック式で A = R[X_1..X_r]/(モニック) → T、A[1/g_1] → B は全射で核は
有限生成、分母を払った関係を加えて A_0 → T、A_0[1/g_1] ≅ B；T の有限個の元 t_j はモニック式と g_1^{N_j} Y_j − a_j で加え、T で零になる有限個の関係も課す。
二対象は A_0 上のテンソルで受け、平行射は差を関係に加えて等化（局所化は常に B）。
規約：A_λ → T の単射性・部分代数であることは要求しない（「有限生成部分代数」では有限表示性が出ない）。
使われ方：各 A_λ に Thm 10.9（A8-2、J = (g_1)）。 -/
theorem exists_finitePresentation_approximation_fixedLocalization (g : R)
    (het : FiniteEtaleAway R (S ⧸ nilradical S) g) :
    let T := integralClosureInLocalization R S g
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I) (F : I ⥤ A_R R)
      (η : F ⟶ (Functor.const I).obj (ofAlgebra R T)),
      Nonempty (IsColimit (Cocone.mk _ η)) ∧ ∀ i, FinitePresentedFinite R (F.obj i) ∧
        let a := (F.obj i).hom.hom g
        let f := T.val.toRingHom.comp (η.app i).right.hom
        Function.Bijective (IsLocalization.Away.lift (S := Localization.Away a) a (g := f)
          (by sorry)) := by
  sorry -- g は B で単元。固定モデルにモニック関係と分母を払った関係を加える。
        -- 共通の初期モデル上のテンソルで二対象を受け、平行射の差を等化。単射性は不要

/-- 概要：g_1-almost 連結性：S_perfd → T̂_perfd は g_1-almost 同型（上）、T̂_perfd は g_1-almost 連結：各 A_λ に Thm 10.9 の連結性（A8-2、A_λ[1/g_1] = B は
R[1/g_1] 上有限エタール）、A5 の filtered 余極限保存を完備圏で使って T̂_perfd ≃ LΛ_p(colim_λ (A_λ)_perfd)、A8-1 の
`isAlmostConnective_completedFilteredColimit`（almost 連結な完備複体は完備 filtered 余極限で閉じる）で T̂_perfd は g_1-almost 連結。
G-A8-8 はここでは使わない（(A_λ)_perfd が perfectoid とはまだ分からない。使えば Thm 10.11 の先取り、W9-III-10）。
方針：A8-2 `perfectoidization_almostConnective_of_finiteEtaleAway`、`perfectoidization_almostIso_integralClosureCompletion`、
`exists_finitePresentation_approximation_fixedLocalization`、A8-1 `isAlmostConnective_completedFilteredColimit`（Codex 第 3 部続き 2 で全接続 ○）。 -/
theorem perfectoidization_almostConnective_of_stratification [Module.Finite R S] [Algebra.FinitePresentation R S]
    {n : ℕ} (g : Fin (n+1) → R) (hg : IsEtaleStratification p R S g) :
    IsAlmostConnective p R hR (Ideal.span {g 0}) (perfdModule p R hR (ofAlgebra R S)) := by
  sorry -- A_λ[1/g₁]≃B に Thm 10.9、G-A8-1 の完備 filtered 余極限の系で T̂_perfd へ。
        -- S→T̂ の almost 同型で戻す。各 A_λ の離散性・perfectoid 性は仮定しない

/-- 概要：Thm 10.11 の連結性：有限表示有限 S で S_perfd 連結（Lemma 10.12 の層別の長さの帰納、Lemma 10.5 で合わせる）。
方針：`exists_finiteEtaleStratification`（A8-3）、上の三つ、A8-1 `connective_iff_almost`。 -/
theorem perfectoidization_connective_of_finitePresentation [Module.Finite R S] [Algebra.FinitePresentation R S]
    (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    Derived.IsConnectiveAt R 0 (perfdModule p R hR (ofAlgebra R S)) := by
  obtain ⟨n, g, hspan, hstrata⟩ := exists_finiteEtaleStratification (R := R) (S := S) p hZp
  sorry -- 長さで帰納。空列なら R は零環、1 層は G-A8-6。帰納段の二条件を Lemma 10.5 で合わせる

/-- 概要：Thm 10.11：S = (整 R 代数)^∧ で Δ_{S/A,perf} は離散な完全 p 完備 δ-A 代数、S_perfd は離散な perfectoid 環。
方針：上の二つ。
規約：原典の形（D67）。
使われ方：`e3Integral`。 -/
theorem prismaticPerfection_discrete_of_integral (h : Algebra.IsIntegral R S) :
    IsDiscretePerfectPerfection p R hR (ofAlgebra R S) := by
  sorry -- 有限表示有限の連結性、G-A8-9・8、d 進 Nakayama と A4 の完全 δ 構造

theorem perfectoidization_isIntegralPerfectoid_of_integral (h : Algebra.IsIntegral R S) :
    let x := completedPerfd p R hR (ofAlgebra R S)
    IsDiscrete R x ∧ IsIntegralPerfectoid (cAlgH0Algebra R x).right p := by
  sorry -- p 完備 perfectoid 基底では p 以外の素数は単元。hZp を供給して有限表示有限の
        -- 連結性を perfectoidization_discrete_of_finitePresentation_connective に渡す

/-- 概要：E3 の `integral`：任意の整 R 代数 S（非完備も）について `IsDiscrete R (e3Perfd S) ∧ IsIntegralPerfectoid (H⁰(e3Perfd S)) p`。
方針：`e3Perfd S = (S^∧)_perfd`（D41、S^∧ = completionRing S = π_0(LΛ_p S)）。Thm 10.11 は原典どおり animated LΛ_p S（整写像の導来 p 完備化）について示し、
Prop 8.5 の系 4（`perfectoidization_piZero`、決定 6）で (LΛ_p S)_perfd ≃ (S^∧)_perfd、`e3H0_of_complete`（A4-3）。
規約：`PerfectoidizationInterfaceCAlg.integral` の型そのまま。
使われ方：A9。 -/
theorem e3Integral (hR : IsIntegralPerfectoid R p := by assumption) (S : A_R R)
    (h : letI : Algebra R S.right := S.hom.hom.toAlgebra; Algebra.IsIntegral R S.right) :
    IsDiscrete R ((e3Perfd p R hR).app _ (nerveVertex S)) ∧
      IsIntegralPerfectoid ((e3H0RingData p R hR).ringFunctor.obj S).right p := by
  sorry -- Thm 10.11 の入力は animated な LΛ_p S。Prop 8.5 系4でその perfd を
        -- π₀(LΛ_p S)=completionRing p S.right の perfd に移し、A4 の完備入力比較で欄を読む

end SerrePositivity.BhattScholze.Perfectoidization.Derived
