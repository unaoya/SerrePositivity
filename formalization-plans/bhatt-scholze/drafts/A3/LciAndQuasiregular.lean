-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Derived.Quasiregular（仮。原典 Example 7.9・Prop 7.10）
-- 設計書：formalization-plans/bhatt-scholze/a3-design.md §2.2・§2.3、単位 A3-3・A3-4。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Semiperfectoid.Perfectoidization
public import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection
public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootPolynomial
public import SerrePositivity.BhattScholze.Prism.PerfectPrismHomLift
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0Comparison
-- 本ファイルは drafts/A3/DiscreteCase.lean、drafts/A0/PrismaticEnvelope.lean、
-- drafts/A2/{DerivedPrismaticCohomology,HodgeTateFiltration,BaseChangeAndTensor}.lean を import する。

/-!
# lci 商と quasiregular semiperfectoid 環の prismatic コホモロジー（BS 著者版 Example 7.9、Prop 7.10）

## 概要
Ex 7.9：f_1,…,f_r ∈ A で f̄ が A/d 上 Koszul 正則、R = A/(d, f) の p ねじれが有界なら、Δ_{R/A} は離散で d ねじれなし、(Δ_R, dΔ_R) は (R/A)_Δ の
始対象で、prismatic envelope A{f/d}^∧ に等しい。Prop 7.10：quasiregular semiperfectoid な S（R → S、A = A_inf(R)）について Δ_{S/A} は離散、
(Δ_S, dΔ_S) は S 上の始 prism（R によらない）、S → Δ_S/d は p 完全忠実平坦。E3 で要るのは S′ = R⟨X_j^{1/p^∞}⟩/(X_j)^∧ の場合で、その完全化は
既存の Cor 7.3 の完全試験 prism への始対象に一致する。

## 方針
Ex 7.9 は原典の形で述べ、証明は普遍の場合 A_univ = A_0{f_1,…,f_r}^∧（A_0 は普遍向き付き prism、f_i は自由 δ 変数）に帰着する。普遍の場合の
envelope は A0-3c の変数の場合。普遍例の E → Δ_univ は HT の離散性・p 正則性の後に作る。一般の B は E の導来底変換として比較し、離散化後に通常の δ 押し出しの普遍性を使う（D40）。
p 反転の議論（[Bha12, Claim 3.30] の変種）は一つの補題に閉じ込める（G-A3-7）。Prop 7.10 は原典どおり T に帰着し、T は完全 prism 上の Ex 7.9。

## 規約
qrsp の定義は BMS19 Def 4.20（余接複体は A2 の Kan 延長、基底 Z_p。D39）。Δ の離散性・prism 性・弱始性は drafts/A3/DiscreteCase。

## 使われ方
A5（Prop 8.5 の semiperfectoid の場合：S′_perfd = R0）、A8（Lemma 10.5、Thm 10.11）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial TensorProduct

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.EInfinity.Perfectoidization SerrePositivity.BhattScholze.PerfectoidizationInterface
open SerrePositivity.DerivedCompletion

variable {p : ℕ} [Fact p.Prime]

/-! ## Example 7.9 -/

section Lci

variable {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P) {r : ℕ} (f : Fin r → A)

/-- Koszul 複体は cohomological に非正。 -/
def IsKoszulRegularModGenerator : Prop :=
  ∀ n : ℕ, Limits.IsZero ((koszulComplex (fun i => Ideal.Quotient.mk P.ideal (f i))).homology (-(n+1 : ℤ)))

def BoundedPTorsion (p : ℕ) (S : Type u) [CommRing S] : Prop :=
  ∃ N : ℕ, ∀ (n : ℕ) (x : S), (p : S)^n * x = 0 → (p : S)^N * x = 0

abbrev lciIdeal := P.ideal ⊔ Ideal.span (Set.range f)
abbrev lciQuotient := A ⧸ lciIdeal P f
instance lciQuotientAlgebra : Algebra (A ⧸ P.ideal) (lciQuotient P f) :=
  (Ideal.Quotient.factor (show P.ideal ≤ lciIdeal P f from le_sup_left)).toAlgebra

/-- D4-02。P₀ と d を保つ射を引数にする。A1 から普遍 A₀ を代入する。 -/
variable {A₀ : Type u} [CommRing A₀] (P₀ : OrientedPrism p A₀) (h₀ : IsBoundedPrism P₀)

abbrev universalLciPrismRing (r : ℕ) := completedFreeDelta P₀ (ULift.{u} (Fin r))
def universalLciPrism (r : ℕ) : OrientedPrism p (universalLciPrismRing P₀ r) where
  deltaStructure := completedFreeDeltaStructure P₀ (ULift.{u} (Fin r))
  generator := completedFreeDeltaBase P₀ (ULift.{u} (Fin r)) P₀.generator
  generator_regular := by sorry -- 自由 δ 多項式環で d₀ は正則、有界基底の完備自由加群でも正則
  complete_p := by sorry -- PDCompletionH0 の p 完備性
  complete_generator := by sorry -- 同じ完備化の d₀ 完備性
  p_mem := by sorry -- P₀.p_mem を δ 基底射で送る

include h₀ in
theorem universalLciPrism_bounded (r : ℕ) : IsBoundedPrism (universalLciPrism P₀ r) := by
  sorry -- mod d₀ は A₀/d₀ 上の多項式環の p 完備化。有界ねじれの上界は基底から継承

def universalLciVariable (r : ℕ) (i : Fin r) : universalLciPrismRing P₀ r :=
  pdCompletionUnit (RelativeFreeDeltaRing (R := A₀) (ULift.{u} (Fin r))) p (algebraMap A₀ _ P₀.generator)
    (MvPolynomial.X (ULift.up i, 0))

def lciClassifyingMap (g : OrientedPrism.Hom P₀ P) (hd : g.toRingHom P₀.generator = P.generator) :
    { u : OrientedPrism.Hom (universalLciPrism P₀ r) P //
      u.toRingHom.comp (completedFreeDeltaBase P₀ (ULift.{u} (Fin r))) = g.toRingHom ∧
      ∀ i, u.toRingHom (universalLciVariable P₀ r i) = f i } := by
  sorry -- 自由 δ 変数を f_i に送り、hd により (p,d₀) 完備化から一意に延長

/-- U→E は A₀ 上の変数 envelope の構造射。平坦性の底は A₀。 -/
structure VariableEnvelope (r : ℕ) where
  ring : CommRingCat.{u}
  Q : OrientedPrism p ring
  η : universalLciPrismRing P₀ r →+* ring
  envelope : IsPrismaticEnvelope P₀ (completedFreeDeltaStructure P₀ (ULift.{u} (Fin r)))
    (completedFreeDeltaBase P₀ (ULift.{u} (Fin r))) (completedFreeDeltaBase_isDeltaHom P₀ (ULift.{u} (Fin r)))
    (variableIdeal P₀ (ULift.{u} (Fin r)) Set.univ) (Ideal.subset_span (Set.mem_insert _ _)) Q η
  bounded : IsBoundedPrism Q
  flat_over_base : letI := (η.comp (completedFreeDeltaBase P₀ (ULift.{u} (Fin r)))).toAlgebra
    IsCompletelyFlat (Ideal.span {(p : A₀), P₀.generator}) ring

def universalEnvelope (r : ℕ) : VariableEnvelope P₀ r := by
  apply Classical.choice
  obtain ⟨C, rc, Q, η, he, hb, hflat⟩ := exists_prismaticEnvelope_of_variables P₀ h₀ (ULift.{u} (Fin r)) Set.univ
  letI := rc
  exact ⟨⟨CommRingCat.of C, Q, η, he, hb, hflat⟩⟩

variable (g : OrientedPrism.Hom P₀ P) (hd : g.toRingHom P₀.generator = P.generator)
abbrev lciMap := (lciClassifyingMap P f P₀ g hd).val
abbrev lciEnvelopeInput :=
  Under.mk (CommRingCat.ofHom (universalEnvelope P₀ h₀ r).η)

/-- B=LΛ_(p,d)(E⊗^L_U A)。ここでは CAlg の完備化で止め、δ 構造は付けない。 -/
def lciDerivedEnvelope : (CompleteCAlg P) _⦋0⦌ :=
  (algebraEmbedding (universalLciPrismRing P₀ r) ≫ cAlgBaseChange (lciMap P f P₀ g hd).toRingHom ≫
    prismCompletion P).app _ (nerveVertex (lciEnvelopeInput P₀ h₀ (r := r)))

/-- Ex 7.9 の比較。変数の envelope E の U→A に沿う完備導来底変換を Δ に同定する。
Koszul 正則性は入力の底変換に使う。B の離散性はこの比較の後に HT で示す。 -/
theorem lciDerivedEnvelope_eq_prismatic (hf : IsKoszulRegularModGenerator P f) :
    Nonempty (VertexIso (lciDerivedEnvelope P f P₀ h₀ g hd)
      ((derivedPrismaticCohomologyDiscrete P hP).app _ (nerveVertex (ofAlgebra _ (lciQuotient P f))))) := by
  sorry -- 普遍比較 E≃Δ_univ を (4) で完備底変換。Koszul 正則性で入力の導来商は R。
        -- 任意の P₀ への変数模型の移送は A0 の variables の底変換を使う

theorem lci_isDiscretePrismatic (hf : IsKoszulRegularModGenerator P f) (hR : BoundedPTorsion p (lciQuotient P f)) :
    IsDiscretePrismatic P hP (lciQuotient P f) := by
  apply isDiscretePrismatic_of_hodgeTate
  sorry -- L=(J/J²)[1] の décalage。各 gr は有限自由で離散。分裂した各段の余極限の
        -- p 冪ねじれの一様上界 hR により導来 p 完備化も離散

/-- 任意の κ に入るとき、指定された H⁰Δ・HT 単位をもつ対象が全有界 prism の中で始。 -/
structure InitialDelta (S : Type u) [CommRing S] [Algebra (A ⧸ P.ideal) S]
    (h : IsDiscretePrismatic P hP S) where
  D : DeltaStructure p (discretePrismaticRing P hP S h)
  base : P.deltaStructure.IsDeltaHom D (discreteBase P hP S)
  frobenius : D.frobeniusLift = discretePrismaticFrobenius P hP S h
  bounded : IsBoundedPrism (discretePrism P hP S h D base)
  initial (κ : Cardinal.{u}) (hs : Cardinal.mk (discretePrismaticRing P hP S h) ≤ κ) :
    Limits.IsInitial (discretePrismOver P hP S h D base κ bounded hs)

/-- E⊗_U A は通常の δ 押し出し。W₂ 切断を二因子で貼り合わせる。 -/
def lciTensorDelta {U E : Type u} [CommRing U] [CommRing E] [Algebra U E] [Algebra U A]
    (DU : DeltaStructure p U) (DE : DeltaStructure p E)
    (hE : DU.IsDeltaHom DE (algebraMap U E)) (hA : DU.IsDeltaHom P.deltaStructure (algebraMap U A)) :
    { D : DeltaStructure p (E ⊗[U] A) //
      DE.IsDeltaHom D Algebra.TensorProduct.includeLeftRingHom ∧
        P.deltaStructure.IsDeltaHom D Algebra.TensorProduct.includeRight.toRingHom } := by
  sorry -- wittTwoMap と両因子の sectionHom は U 上一致するので環の押し出しから切断を得る

theorem lciTensorDelta_map_iff {U E T : Type u} [CommRing U] [CommRing E] [CommRing T]
    [Algebra U E] [Algebra U A] (DU : DeltaStructure p U) (DE : DeltaStructure p E)
    (hE : DU.IsDeltaHom DE (algebraMap U E)) (hA : DU.IsDeltaHom P.deltaStructure (algebraMap U A))
    (DT : DeltaStructure p T) (v : (E ⊗[U] A) →+* T) :
    (lciTensorDelta P DU DE hE hA).val.IsDeltaHom DT v ↔
      DE.IsDeltaHom DT (v.comp Algebra.TensorProduct.includeLeftRingHom) ∧
      P.deltaStructure.IsDeltaHom DT (v.comp Algebra.TensorProduct.includeRight.toRingHom) := by
  sorry -- isDeltaHom_iff_sectionHom_comp。W₂(T) への二射をテンソルの両因子で比較

abbrev IsLciEnvelope {B : Type u} [CommRing B] (Q : OrientedPrism p B) (η : A →+* B) :=
  IsPrismaticEnvelope P P.deltaStructure (RingHom.id A) P.deltaStructure.isDeltaHom_id
    (lciIdeal P f) (show P.generator ∈ lciIdeal P f from (show P.ideal ≤ lciIdeal P f from le_sup_left) (Ideal.subset_span (by simp))) Q η

/-- 通常の押し出し N の (p,d) 完備化の H⁰。A の単位は右因子から入る。 -/
def lciCompletedOrdinary : A_R A := by
  let U := universalLciPrismRing P₀ r
  let E := universalEnvelope P₀ h₀ r
  letI : Algebra U E.ring := E.η.toAlgebra
  letI : Algebra U A := (lciMap P f P₀ g hd).toRingHom.toAlgebra
  let N := E.ring ⊗[U] A
  let j : A →+* N := Algebra.TensorProduct.includeRight.toRingHom
  letI := pdCompletionCommRing N p (j P.generator)
  exact Under.mk (CommRingCat.ofHom ((pdCompletionUnit N p (j P.generator)).comp j))

/-- 導来テンソルから通常テンソルへの増大に沿う比較。高次 Tor の消滅を仮定しない。 -/
theorem lciCompletionH0Comparison (hf : IsKoszulRegularModGenerator P f)
    (h : IsDiscretePrismatic P hP (lciQuotient P f)) :
    Nonempty (VertexIso ((prismCompleteInclusion P).app _ (lciDerivedEnvelope P f P₀ h₀ g hd))
      ((algebraEmbedding A).app _ (nerveVertex (lciCompletedOrdinary P f P₀ h₀ g hd)))) := by
  sorry -- lciDerivedEnvelope_eq_prismatic と h で B は離散。導来テンソル→N は非正で H⁰ 同型。
        -- derivedComplexCompletion_h0_map_isIso を p,d の順に適用して環の比較に移す

/-- G-A3-10。導来完備テンソルの比較後に H⁰ と W₂ を使う。 -/
theorem lciDerivedEnvelope_isEnvelope_of_discrete (hf : IsKoszulRegularModGenerator P f)
    (hR : BoundedPTorsion p (lciQuotient P f)) (h : IsDiscretePrismatic P hP (lciQuotient P f)) :
    let R := lciQuotient P f
    Nonempty (VertexIso ((prismCompleteInclusion P).app _ (lciDerivedEnvelope P f P₀ h₀ g hd))
      ((algebraEmbedding A).app _ (nerveVertex (discreteDeltaAlgebra P hP R)))) ∧
      ∃ t : InitialDelta P hP R h, IsLciEnvelope P f (discretePrism P hP R h t.D t.base) (discreteBase P hP R) := by
  sorry -- lciDerivedEnvelope_eq_prismatic と discreteDeltaIso。E⊗^L_U A→E⊗_U A の H⁰ 同型は
        -- derivedComplexCompletion_h0_map_isIso を p,d に適用して保たれる。lciTensorDelta と
        -- existsUnique_deltaPDCompletionHom から全 prism への一意な δ 射、有界性は HT と hR

/-- 普遍変数の δ 除算 E→H⁰Δ の mod d。比較の向きと f/d の像は envelope の普遍性で固定する。 -/
def universalModDComparison (r : ℕ)
    (hU : IsBoundedPrism (universalLciPrism P₀ r))
    (h : IsDiscretePrismatic (universalLciPrism P₀ r) hU
      (lciQuotient (universalLciPrism P₀ r) (universalLciVariable P₀ r)))
    (D : DeltaStructure p (discretePrismaticRing _ hU _ h))
    (hD : (universalLciPrism P₀ r).deltaStructure.IsDeltaHom D (discreteBase _ hU _)) :
    let U := universalLciPrism P₀ r
    let R := lciQuotient U (universalLciVariable P₀ r)
    let E := universalEnvelope P₀ h₀ r
    E.ring ⧸ E.Q.ideal →+* discretePrismaticRing U hU R h ⧸ (discretePrism U hU R h D hD).ideal := by
  let U := universalLciPrism P₀ r
  let R := lciQuotient U (universalLciVariable P₀ r)
  let E := universalEnvelope P₀ h₀ r
  let Q := discretePrism U hU R h D hD
  have lift := E.envelope.lift Q (discreteBase U hU R) hD
    (by sorry) -- 分類射は d₀ を Q.generator に送る
    (by sorry) -- HT 単位の構造三角から各 f_i は mod d で零
  exact Ideal.quotientMap Q.ideal lift.exists.choose (by
    sorry) -- lift は U 上の射、E のイデアルは η(d₀) で生成される

/-- G-A3-7。p ねじれなしの普遍例。Banach 代数の生成の計算は証明予定。 -/
theorem lci_envelope_surjective_invert_p_universal (r : ℕ)
    (hU : IsBoundedPrism (universalLciPrism P₀ r))
    (h : IsDiscretePrismatic (universalLciPrism P₀ r) hU
      (lciQuotient (universalLciPrism P₀ r) (universalLciVariable P₀ r)))
    (hpU : NoPTorsion p (universalLciPrismRing P₀ r ⧸ (universalLciPrism P₀ r).ideal))
    (hpR : NoPTorsion p (lciQuotient (universalLciPrism P₀ r) (universalLciVariable P₀ r)))
    (D : DeltaStructure p (discretePrismaticRing _ hU _ h))
    (hD : (universalLciPrism P₀ r).deltaStructure.IsDeltaHom D (discreteBase _ hU _))
    (hφ : D.frobeniusLift = discretePrismaticFrobenius _ hU _ h) :
    let q := universalModDComparison P₀ h₀ r hU h D hD
    Function.Surjective (Localization.awayMap q (p : _)) := by
  sorry -- bar/Koszul 計算で f_i/d が gr¹ の基底 f_i mod J² に写る。p 反転後に生成する
        -- 稠密な部分代数を含み、retraction で像が閉。Bha12 Claim 3.30 の変種をここで証明する

include P₀ h₀ g hd in
/-- Ex 7.9。A 代数としての H⁰Δ とその構造射を envelope として特徴付ける。
この包からの一意な射で、有界な site の全対象に対する始性を得る。 -/
theorem prismaticCohomology_lci_eq_envelope (hf : IsKoszulRegularModGenerator P f)
    (hR : BoundedPTorsion p (lciQuotient P f)) :
    let R := lciQuotient P f
    let h := lci_isDiscretePrismatic P hP f hf hR
    ∃ t : InitialDelta P hP R h, IsLciEnvelope P f (discretePrism P hP R h t.D t.base) (discreteBase P hP R) := by
  have hc := lciDerivedEnvelope_isEnvelope_of_discrete P hP f P₀ h₀ g hd hf hR
    (lci_isDiscretePrismatic P hP f hf hR)
  exact hc.2

/-- 元の存在補題。普遍性の標的には有界性を課さない。 -/
theorem exists_lciEnvelope (hf : IsKoszulRegularModGenerator P f) :
    ∃ (B : CommRingCat.{u}) (Q : OrientedPrism p B) (η : A →+* B), IsLciEnvelope P f Q η := by
  sorry -- (A,(d,f)) の δ 除算と完備化の普遍性。上の有界な site の始性とは別の存在補題

end Lci

/-! ## quasiregular semiperfectoid 環と Prop 7.10 -/

section Quasiregular

abbrev PadicBase (p : ℕ) [Fact p.Prime] := ULift.{u} (PadicInt p)

/-- 導来 p 完備な離散環の標準 ℤ_p 作用。 -/
def padicBaseAlgebra (S : Type u) [CommRing S]
    (h : IsModuleComplete S (p : S) (ModuleCat.of S S)) : Algebra (PadicBase.{u} p) S := by
  sorry -- 要確認：主元完備化へ。ℤ→S を主元 p の完備化単位に沿って一意に延長し、ℤ_p と同定

/-- D39。L̂_{S/ℤ_p}[−1] の導来 mod p が次数零の平坦な S/p 加群。 -/
def CotangentPCompletelyFlat (S : Type u) [CommRing S]
    (h : IsModuleComplete S (p : S) (ModuleCat.of S S)) : Prop :=
  letI := padicBaseAlgebra (p := p) S h
  let M := (cotangentWedgeAtAlgebra p (PadicBase.{u} p) S 1).1
  let I : Ideal S := Ideal.span {(p : S)}
  let X := (completeDInclusion p S ≫ loopFunctor _ ≫ derivedInfinityBaseChange (Ideal.Quotient.mk I)).app _ M
  ∃ N : ModuleCat.{u} (S ⧸ I), Module.Flat (S ⧸ I) N ∧ Nonempty (VertexIso X (moduleHeartVertex _ N))

structure IsQuasiregularSemiperfectoid (S : Type u) [CommRing S] : Prop where
  pComplete : IsModuleComplete S (p : S) (ModuleCat.of S S)
  semiperfectoid : ∃ (T : CommRingCat.{u}) (q : T →+* S), IsIntegralPerfectoid T p ∧ Function.Surjective q
  boundedTorsion : BoundedPTorsion p S
  cotangent_flat : CotangentPCompletelyFlat (p := p) S pComplete

variable (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-- 零環の枝では R 自身、それ以外は W(R^♭)。 -/
def ainfCoefficients (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] : CommRingCat.{u} := by
  classical
  exact if hp : IsUnit (p : R) then CommRingCat.of R else
    letI : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    CommRingCat.of (WittVector p (PreTilt R p))

abbrev ainfPrismRing := (ainfCoefficients p R : Type u)

def ainfTheta (hR : IsIntegralPerfectoid R p) : ainfPrismRing (p := p) R →+* R := by
  classical
  by_cases hp : IsUnit (p : R)
  · simpa [ainfPrismRing, ainfCoefficients, hp] using RingHom.id R
  · letI : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    letI : IsAdicComplete (Ideal.span {(p : R)}) R := by
      sorry -- hR の非零枝の完備性（零環なら hp と矛盾）
    simpa [ainfPrismRing, ainfCoefficients, hp] using WittVector.fontaineTheta R p

def ainfDelta (hR : IsIntegralPerfectoid R p) : DeltaStructure p (ainfPrismRing (p := p) R) := by
  classical
  by_cases hp : IsUnit (p : R)
  · sorry -- この枝の perfectoid R は零環で WittTwo 切断は一意
  · letI : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    simpa [ainfPrismRing, ainfCoefficients, hp] using wittDeltaStructure p (PreTilt R p)

structure AinfData where
  prism : OrientedPrism p (ainfPrismRing (p := p) R)
  delta_eq : prism.deltaStructure = ainfDelta R hR
  perfect : prism.deltaStructure.IsPerfect
  bounded : IsBoundedPrism prism
  residue : ainfPrismRing (p := p) R ⧸ prism.ideal ≃+* R
  theta_eq : residue.toRingHom.comp (Ideal.Quotient.mk prism.ideal) = ainfTheta R hR

def ainfData : AinfData R hR := by
  sorry -- 非零枝は exists_distinguished_fontaine_kernel_generator と完全 Witt δ 環で θ の核を生成。
        -- Subsingleton R では零 prism。両枝で θ の全射性から residue を取る

abbrev ainfPrism := (ainfData R hR).prism
variable (S : Type u) [CommRing S] [Algebra R S]

/-- R 代数を A_inf(R)/d 代数として読む。 -/
def ainfResidueAlgebra : Algebra (ainfPrismRing (p := p) R ⧸ (ainfPrism R hR).ideal) S :=
  ((algebraMap R S).comp (ainfData R hR).residue.toRingHom).toAlgebra

local instance : Algebra (ainfPrismRing (p := p) R ⧸ (ainfPrism R hR).ideal) S := ainfResidueAlgebra R hR S

abbrev QrspDiscrete := IsDiscretePrismatic (ainfPrism R hR) (ainfData R hR).bounded S

/-- Prop 7.10(a)。一般の qrsp の有界ねじれを使い、完備余極限後の Δ̄ の離散性を示す。 -/
theorem qrsp_isDiscretePrismatic (hS : IsQuasiregularSemiperfectoid (p := p) S) :
    QrspDiscrete R hR S := by
  apply isDiscretePrismatic_of_hodgeTate
  sorry -- 推移三角と décalage で各 gr が p 完全平坦。hS.boundedTorsion と完備余極限で HT が離散

/-- HT の単位 S→H⁰(Δ̄)=H⁰(Δ)/d。δ 構造を選ぶ前に使える。 -/
def qrspHTMap (h : QrspDiscrete R hR S) :
    let P := ainfPrism R hR
    let C := discreteDeltaAlgebra P (ainfData R hR).bounded S
    S →+* C.right ⧸ Ideal.span {C.hom.hom P.generator} :=
  (discreteHTArrow (ainfPrism R hR) (ainfData R hR).bounded S h).val.right.hom

/-- Prop 7.10(a) の平坦性は S 上で測り、その S 作用には HT 単位を使う。 -/
theorem qrsp_completelyFaithfullyFlat (hS : IsQuasiregularSemiperfectoid (p := p) S) :
    let P := ainfPrism R hR
    let C := discreteDeltaAlgebra P (ainfData R hR).bounded S
    letI := (qrspHTMap R hR S (qrsp_isDiscretePrismatic R hR S hS)).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : S)}) (C.right ⧸ Ideal.span {C.hom.hom P.generator}) := by
  sorry -- mod p で各 gr は平坦、Fil₀ は S/p。単位を含む分裂 filtration と完備余極限

/-- 任意個の根付き変数。A5 の rootPolynomialFamily と同じモノイド環を先に使う。 -/
abbrev rootPolynomials (J : Type u) := AddMonoidAlgebra R (J →₀ Andre.powerRootExponentMonoid p (Fact.out : p.Prime).pos)
abbrev rootBase (J : Type u) := ↥(completionRing p (CommRingCat.of (rootPolynomials (p := p) R J)))
instance (J : Type u) : Algebra R (rootBase (p := p) R J) :=
  ((completionUnit p _).hom.comp (algebraMap R (rootPolynomials (p := p) R J))).toAlgebra

def rootX {J : Type u} (j : J) (n : ℕ) : rootBase (p := p) R J := by
  classical
  exact (completionUnit p _).hom (AddMonoidAlgebra.single (Finsupp.single j
    (Andre.powerRootVariableExponent p (Fact.out : p.Prime).pos n)) (1 : R))

include hR in
theorem rootBase_perfectoid (J : Type u) : IsIntegralPerfectoid (rootBase (p := p) R J) p := by
  sorry -- 完備化したモノイド環。mod p の各単項式に p 乗根があり、θ の核の生成元を R から移す

def rootRelations {J : Type u} (f : J → R) : Ideal (rootBase (p := p) R J) :=
  Ideal.span (Set.range (fun j => rootX (p := p) R j 0 - algebraMap R _ (f j)))

abbrev rootQuotient {J : Type u} (f : J → R) :=
  ↥(completionRing p (CommRingCat.of (rootBase (p := p) R J ⧸ rootRelations (p := p) R f)))

def rootQuotientMap {J : Type u} (f : J → R) :
    rootBase (p := p) R J →+* rootQuotient (p := p) R f :=
  (completionUnit p _).hom.comp (Ideal.Quotient.mk (rootRelations (p := p) R f))

instance {J : Type u} (f : J → R) : Algebra R (rootQuotient (p := p) R f) :=
  ((rootQuotientMap (p := p) R f).comp (algebraMap R _)).toAlgebra

abbrev regularSemiperfectoid (r : ℕ) (f : Fin r → R) :=
  rootQuotient (p := p) R (fun i : ULift.{u} (Fin r) => f i.down)

/-- 完全基底間の射を剰余環での構造射から一意に持ち上げる。 -/
def rootBasePrismMap (J : Type u) :
    OrientedPrism.Hom (ainfPrism R hR) (ainfPrism _ (rootBase_perfectoid R hR J)) := by
  let R' := rootBase (p := p) R J
  let h' := rootBase_perfectoid R hR J
  let q := (ainfData R' h').residue.symm.toRingHom.comp
    ((algebraMap R R').comp (ainfData R hR).residue.toRingHom)
  exact (Andre.existsUnique_perfectPrismHomLift_to_bounded (ainfPrism R hR) (ainfData R hR).perfect
    (ainfPrism R' h') (ainfData R' h').bounded q).exists.choose

/-- T での G-A2-10 と、A′ 上の Ex 7.9。R 上でも全有界試験 prism に対して始。 -/
theorem regularSemiperfectoid_prismatic (r : ℕ) (f : Fin r → R) :
    let R' := rootBase (p := p) R (ULift.{u} (Fin r))
    let h' := rootBase_perfectoid R hR (ULift.{u} (Fin r))
    let T := regularSemiperfectoid (p := p) R r f
    let q := rootQuotientMap (p := p) R (fun i : ULift.{u} (Fin r) => f i.down)
    let P' := ainfPrism R' h'
    let t : A_R (ainfPrismRing (p := p) R' ⧸ P'.ideal) :=
      Under.mk (CommRingCat.ofHom (q.comp (ainfData R' h').residue.toRingHom))
    let u := rootBasePrismMap R hR (ULift.{u} (Fin r))
    IsIso (functorHomEvaluate (perfectBaseComparison _ (ainfData R hR).bounded P' (ainfData R' h').bounded u)
      ((discreteToAnimated _).app _ (nerveVertex t))) ∧
      (letI : Algebra (ainfPrismRing (p := p) R' ⧸ P'.ideal) T := t.hom.hom.toAlgebra
       ∃ (w : Fin r → ainfPrismRing (p := p) R') (h : IsDiscretePrismatic P' (ainfData R' h').bounded T)
         (t₀ : InitialDelta P' (ainfData R' h').bounded T h),
         (∀ i, ainfTheta R' h' (w i) = rootX (p := p) R (ULift.up i : ULift.{u} (Fin r)) 0 - algebraMap R R' (f i)) ∧
           IsLciEnvelope P' w (discretePrism P' (ainfData R' h').bounded T h t₀.D t₀.base)
             (discreteBase P' (ainfData R' h').bounded T)) ∧
      ∃ h : QrspDiscrete R hR T, Nonempty (InitialDelta (ainfPrism R hR) (ainfData R hR).bounded T h) := by
  sorry -- T は R′ の X_i−f_i による Koszul 正則商。A′ で Ex 7.9、A へは
        -- perfectBaseComparison_isIso（(4) と乗法）。Lemma 4.8 の一意持ち上げで始性を移す

/-- 原典 Prop 7.10(b) の一般形の記録（W9-I-43、別単位）。E3 に使うのは下の T・S′ の始性。 -/
theorem qrsp_initial (hS : IsQuasiregularSemiperfectoid (p := p) S) :
    Nonempty (InitialDelta (ainfPrism R hR) (ainfData R hR).bounded S (qrsp_isDiscretePrismatic R hR S hS)) := by
  sorry -- 別単位：一般の qrsp には原典の自然な δ 自己準同型の議論が必要。T の帰着のみでは示さない

/-- 完全化の台と構造射。理想の生成元は完全化単位で送った d。 -/
def perfectedCoefficients {B : Type u} [CommRing B] (Q : OrientedPrism p B) : CommRingCat.{u} := by
  let E := Q.deltaStructure
  let b := deltaPerfectionOf E 0 Q.generator
  letI := pdCompletionCommRing (DeltaPerfection E) p b
  exact CommRingCat.of (PDCompletionH0 (DeltaPerfection E) p b)

def perfectedPrism {B : Type u} [CommRing B] (Q : OrientedPrism p B) :
    OrientedPrism p (perfectedCoefficients Q) :=
  perfectDeltaPDPrism (deltaPerfectionStructure Q.deltaStructure) (deltaPerfection_isPerfect Q.deltaStructure)
    (deltaPerfectionOf Q.deltaStructure 0 Q.generator)
    ((deltaPerfectionOf_isDeltaHom Q.deltaStructure 0).map_isDistinguished Q.isDistinguished_generator)

theorem perfectedPrism_isPerfect {B : Type u} [CommRing B] (Q : OrientedPrism p B) :
    (perfectedPrism Q).deltaStructure.IsPerfect :=
  perfectDeltaPDPrism_isPerfect (deltaPerfectionStructure Q.deltaStructure) (deltaPerfection_isPerfect Q.deltaStructure)
    (deltaPerfectionOf Q.deltaStructure 0 Q.generator)
    ((deltaPerfectionOf_isDeltaHom Q.deltaStructure 0).map_isDistinguished Q.isDistinguished_generator)

def toPerfectedPrism {B : Type u} [CommRing B] (Q : OrientedPrism p B) :
    OrientedPrism.Hom Q (perfectedPrism Q) where
  toRingHom := (pdCompletionUnit _ p (deltaPerfectionOf Q.deltaStructure 0 Q.generator)).comp
    (deltaPerfectionOf Q.deltaStructure 0)
  map_delta := (pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom _ 0)
  ideal_le := by sorry -- perfectDeltaPDPrism_generator は上の構造射での Q.generator の像

/-- S′ 上の初期 prism の完全化の商への単位、非零環の Cor 7.3 の候補との S′ 上の同型。 -/
def IsCor73Comparison {B T C : Type u} [CommRing B] [CommRing T] [CommRing C]
    (P' : OrientedPrism p B) (h' : P'.deltaStructure.IsPerfect)
    (r : B →+* T) (hr : Function.Surjective r) (Q : OrientedPrism p C) (η : T →+* C ⧸ Q.ideal) : Prop :=
  letI := perfectDeltaDivisionPrismCommRing P'.deltaStructure P'.generator (RingHom.ker r)
  let V := perfectDeltaDivisionPrism P'.deltaStructure P'.generator P'.isDistinguished_generator (RingHom.ker r)
  let q := perfectPrismQuotientPerfectoidizationMap P' h' r hr
  ∃! F : OrientedPrism.Hom Q V, F.quotientMap.comp η = q ∧
    ∃ G : OrientedPrism.Hom V Q, G.comp F = OrientedPrism.Hom.id Q ∧ F.comp G = OrientedPrism.Hom.id V

theorem rootQuotient_initial (J : Type u) :
    let S' := rootQuotient (p := p) R (fun _ : J => 0)
    ∃ h : QrspDiscrete R hR S', Nonempty (InitialDelta (ainfPrism R hR) (ainfData R hR).bounded S' h) := by
  sorry -- 有限部分集合の regularSemiperfectoid_prismatic、Δ の完備 filtered 余極限保存。
        -- δ 射の両立族を完備化へ延長して始性を得る（一般 qrsp の始性は使わない）

/-- W9-I-43・44。有限部分族の始性を完備 filtered 余極限へ移し、S′ の上で比較する。 -/
theorem rootQuotient_prismatic_perfection_eq (J : Type u) :
    let R' := rootBase (p := p) R J
    let S' := rootQuotient (p := p) R (fun _ : J => 0)
    let h' := rootBase_perfectoid R hR J
    let P' := ainfPrism R' h'
    let r := (rootQuotientMap (p := p) R (fun _ : J => 0)).comp (ainfTheta R' h')
    ∃ (h : QrspDiscrete R hR S') (d : InitialDelta (ainfPrism R hR) (ainfData R hR).bounded S' h)
      (hr : Function.Surjective r),
      let Q := discretePrism (ainfPrism R hR) (ainfData R hR).bounded S' h d.D d.base
      let η := (toPerfectedPrism Q).quotientMap.comp
        (discreteHTMap (ainfPrism R hR) (ainfData R hR).bounded S' h d.D d.base)
      r P'.generator = 0 ∧ IsPerfectoidization p η ∧
        ((Subsingleton R' ∧ Subsingleton S' ∧ Subsingleton (perfectedCoefficients Q ⧸ (perfectedPrism Q).ideal)) ∨
          (Nontrivial R' ∧ ¬IsUnit (p : ainfPrismRing (p := p) R' ⧸ P'.ideal) ∧
            IsCor73Comparison P' (ainfData R' h').perfect r hr (perfectedPrism Q) η)) := by
  obtain ⟨h, ⟨d⟩⟩ := rootQuotient_initial R hR J
  refine ⟨h, d, ?_, ?_⟩
  · sorry -- R′ 完備なので商の p 完備化への射は全射。θ の全射性と合成
  · sorry -- existsUnique_deltaPerfectionPDCompletionHom で完全標的への始性に移す。
        -- r=θ の後に商と完備化。R′≠0 では剰余環の p は非単元で Cor 7.3 の入口に
        -- exists_perfectoidization_of_perfectPrism_quotient に hr と r(d′)=0 を渡す。
        -- 両普遍性と Lemma 4.8 で S′ 上の完全 prism の唯一の同型。R′=0 では全て零環

end Quasiregular

end SerrePositivity.BhattScholze.Prismatic
