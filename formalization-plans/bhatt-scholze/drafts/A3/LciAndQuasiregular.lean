-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Derived.Quasiregular（仮。原典 Example 7.9・Prop 7.10）
-- 設計書：formalization-plans/bhatt-scholze/a3-design.md §2.2・§2.3、単位 A3-3・A3-4。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.BhattScholze.Delta.Basic.Tensor
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDelta
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaResidue
public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Bounded
public import SerrePositivity.BhattScholze.Semiperfectoid.Basic
public import SerrePositivity.BhattScholze.Semiperfectoid.AinfClassicalMaps

public import SerrePositivity.BhattScholze.Semiperfectoid.Perfectoidization
public import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootPolynomial
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PadicIntMap
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

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

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

/-- BS 著者版 Definition 1.4 の有界なp冪ねじれ。本体の述語への互換の略記。 -/
abbrev BoundedPTorsion (p : ℕ) (S : Type u) [CommRing S] : Prop :=
  SerrePositivity.HasBoundedPTorsion p S

abbrev lciIdeal := P.ideal ⊔ Ideal.span (Set.range f)
abbrev lciQuotient := A ⧸ lciIdeal P f
instance lciQuotientAlgebra : Algebra (A ⧸ P.ideal) (lciQuotient P f) :=
  (Ideal.Quotient.factor (show P.ideal ≤ lciIdeal P f from le_sup_left)).toAlgebra

variable {A₀ : Type u} [CommRing A₀] (P₀ : OrientedPrism p A₀) (h₀ : IsBoundedPrism P₀)

abbrev universalLciPrismRing (r : ℕ) := completedFreeDelta P₀ (ULift.{u} (Fin r))
include h₀ in
/-- BS 著者版 Example 7.9。P₀ と d を保つ射を引数にする。A1 から普遍 A₀ を代入する。 -/
def universalLciPrism (r : ℕ) : OrientedPrism p (universalLciPrismRing P₀ r) where
  deltaStructure := completedFreeDeltaStructure P₀ (ULift.{u} (Fin r))
  generator := completedFreeDeltaBase P₀ (ULift.{u} (Fin r)) P₀.generator
  generator_regular := completedFreeDelta_generator_regular P₀ h₀ (ULift.{u} (Fin r))
  complete_p := completedFreeDelta_complete_p P₀ (ULift.{u} (Fin r))
  complete_generator := completedFreeDelta_complete_generator P₀ (ULift.{u} (Fin r))
  p_mem := ((completedFreeDeltaBase_isDeltaHom P₀ (ULift.{u} (Fin r))).map_isDistinguished
    P₀.isDistinguished_generator).p_mem_span

include h₀ in
theorem universalLciPrism_bounded (r : ℕ) : IsBoundedPrism (universalLciPrism P₀ h₀ r) :=
  completedFreeDelta_residue_bounded P₀ h₀ (ULift.{u} (Fin r))

def universalLciVariable (r : ℕ) (i : Fin r) : universalLciPrismRing P₀ r :=
  pdCompletionUnit (RelativeFreeDeltaRing (R := A₀) (ULift.{u} (Fin r))) p (algebraMap A₀ _ P₀.generator)
    (MvPolynomial.X (ULift.up i, 0))

def lciClassifyingMap (g : OrientedPrism.Hom P₀ P) (hd : g.toRingHom P₀.generator = P.generator) :
    { u : OrientedPrism.Hom (universalLciPrism P₀ h₀ r) P //
      u.toRingHom.comp (completedFreeDeltaBase P₀ (ULift.{u} (Fin r))) = g.toRingHom ∧
      ∀ i, u.toRingHom (universalLciVariable P₀ r i) = f i } := by
  have hc : IsModuleComplete A (g.toRingHom P₀.generator) (ModuleCat.of A A) := by
    simpa only [hd] using P.complete_generator
  let hex := existsUnique_completedFreeDeltaHom P₀ (ULift.{u} (Fin r))
    P.deltaStructure g.toRingHom g.map_delta P.complete_p hc (fun i => f i.down)
  let u := hex.exists.choose
  have hu := hex.exists.choose_spec
  have hgen : u (completedFreeDeltaBase P₀ (ULift.{u} (Fin r)) P₀.generator) = P.generator :=
    (RingHom.congr_fun hu.2.1 P₀.generator).trans hd
  let v : OrientedPrism.Hom (universalLciPrism P₀ h₀ r) P :=
    { toRingHom := u
      map_delta := hu.1
      ideal_le := by
        apply Ideal.span_le.mpr
        rintro x (rfl : x = (universalLciPrism P₀ h₀ r).generator)
        change u (completedFreeDeltaBase P₀ (ULift.{u} (Fin r)) P₀.generator) ∈ P.ideal
        rw [hgen]
        exact Ideal.mem_span_singleton_self _ }
  refine ⟨v, hu.2.1, ?_⟩
  intro i
  simpa only [v, u, hex, universalLciVariable, completedFreeDeltaVariable] using hu.2.2 (ULift.up i)

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
abbrev lciMap := (lciClassifyingMap (h₀ := h₀) P f P₀ g hd).val
abbrev lciEnvelopeInput :=
  Under.mk (CommRingCat.ofHom (universalEnvelope P₀ h₀ r).η)

/-- B=LΛ_(p,d)(E⊗^L_U A)。ここでは CAlg の完備化で止め、δ 構造は付けない。 -/
def lciDerivedEnvelope : (CompleteCAlg (E := E) P) _⦋0⦌ :=
  (E.discrete (universalLciPrismRing P₀ r) ≫ cAlgBaseChange (E := E) (lciMap (h₀ := h₀) P f P₀ g hd).toRingHom ≫
    prismCompletion (E := E) P).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (lciEnvelopeInput P₀ h₀ (r := r)))

/-- Ex 7.9 の比較。変数の envelope E の U→A に沿う完備導来底変換を Δ に同定する。
Koszul 正則性は入力の底変換に使う。B の離散性はこの比較の後に HT で示す。 -/
theorem lciDerivedEnvelope_eq_prismatic (hf : IsKoszulRegularModGenerator P f) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (lciDerivedEnvelope (E := E) P f P₀ h₀ g hd)
      ((derivedPrismaticCohomologyDiscrete (E := E) P hP).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra _ (lciQuotient P f))))) := by
  sorry -- 普遍比較 E≃Δ_univ を (4) で完備底変換。Koszul 正則性で入力の導来商は R。
        -- 任意の P₀ への変数模型の移送は A0 の variables の底変換を使う

/-- BS 著者版 Example 7.9 の Koszul 正則な商の離散性。
剰余の有界な p 冪ねじれを仮定し、完備化後の離散性は将来の HT 比較に残す。 -/
theorem lci_isDiscretePrismatic (hf : IsKoszulRegularModGenerator P f) (hR : BoundedPTorsion p (lciQuotient P f)) :
    IsDiscretePrismatic (E := E) P hP (lciQuotient P f) := by
  apply isDiscretePrismatic_of_hodgeTate (E := E)
  sorry -- L=(J/J²)[1] の décalage。各 gr は有限自由で離散。分裂した各段の余極限の
        -- p 冪ねじれの一様上界 hR により導来 p 完備化も離散

/-- 任意の κ に入るとき、指定された H⁰Δ・HT 単位をもつ対象が全有界 prism の中で始。 -/
structure InitialDelta (S : Type u) [CommRing S] [Algebra (A ⧸ P.ideal) S]
    (h : IsDiscretePrismatic (E := E) P hP S) where
  D : DeltaStructure p (discretePrismaticRing (E := E) P hP S h)
  base : P.deltaStructure.IsDeltaHom D (discreteBase (E := E) P hP S)
  frobenius : D.frobeniusLift = discretePrismaticFrobenius (E := E) P hP S h
  bounded : IsBoundedPrism (discretePrism (E := E) P hP S h D base)
  initial (κ : Cardinal.{u}) (hs : Cardinal.mk (discretePrismaticRing (E := E) P hP S h) ≤ κ) :
    Limits.IsInitial (discretePrismOver (E := E) P hP S h D base κ bounded hs)

/-- E⊗_U A は通常の δ 押し出し。W₂ 切断を二因子で貼り合わせる。 -/
def lciTensorDelta {U datum : Type u} [CommRing U] [CommRing datum] [Algebra U datum] [Algebra U A]
    (DU : DeltaStructure p U) (DE : DeltaStructure p datum)
    (hE : DU.IsDeltaHom DE (algebraMap U datum)) (hA : DU.IsDeltaHom P.deltaStructure (algebraMap U A)) :
    { D : DeltaStructure p (datum ⊗[U] A) //
      DE.IsDeltaHom D Algebra.TensorProduct.includeLeftRingHom ∧
        P.deltaStructure.IsDeltaHom D Algebra.TensorProduct.includeRight.toRingHom } := by
  exact ⟨tensorDeltaStructure DU DE P.deltaStructure hE hA,
    tensorDeltaStructure_includeLeft DU DE P.deltaStructure hE hA,
    tensorDeltaStructure_includeRight DU DE P.deltaStructure hE hA⟩

/-- BS 著者版 Example 7.9 に用いる通常の δ テンソルの写像の法則。
両因子で δ 射であることと同値で、本体の押し出しの法則を使う。 -/
theorem lciTensorDelta_map_iff {U datum T : Type u} [CommRing U] [CommRing datum] [CommRing T]
    [Algebra U datum] [Algebra U A] (DU : DeltaStructure p U) (DE : DeltaStructure p datum)
    (hE : DU.IsDeltaHom DE (algebraMap U datum)) (hA : DU.IsDeltaHom P.deltaStructure (algebraMap U A))
    (DT : DeltaStructure p T) (v : (datum ⊗[U] A) →+* T) :
    (lciTensorDelta P DU DE hE hA).val.IsDeltaHom DT v ↔
      DE.IsDeltaHom DT (v.comp Algebra.TensorProduct.includeLeftRingHom) ∧
      P.deltaStructure.IsDeltaHom DT (v.comp Algebra.TensorProduct.includeRight.toRingHom) := by
  exact tensorDeltaStructure_isDeltaHom_iff DU DE P.deltaStructure hE hA DT v

/-- BS 著者版 Example 7.9 の関係式の prismatic envelope の普遍性。
基底 A 自身を δ 代数として、既存の IsPrismaticEnvelope に代入する。 -/
abbrev IsLciEnvelope {B : Type u} [CommRing B] (Q : OrientedPrism p B) (η : A →+* B) :=
  IsPrismaticEnvelope P P.deltaStructure (RingHom.id A) P.deltaStructure.isDeltaHom_id
    (lciIdeal P f) (show P.generator ∈ lciIdeal P f from (show P.ideal ≤ lciIdeal P f from le_sup_left) (Ideal.subset_span (by simp))) Q η

/-- 通常の押し出し N の (p,d) 完備化の H⁰。A の単位は右因子から入る。 -/
def lciCompletedOrdinary : A_R A := by
  let U := universalLciPrismRing P₀ r
  let datum := universalEnvelope P₀ h₀ r
  letI : Algebra U datum.ring := datum.η.toAlgebra
  letI : Algebra U A := (lciMap (h₀ := h₀) P f P₀ g hd).toRingHom.toAlgebra
  let N := datum.ring ⊗[U] A
  let j : A →+* N := Algebra.TensorProduct.includeRight.toRingHom
  letI := pdCompletionCommRing N p (j P.generator)
  exact Under.mk (CommRingCat.ofHom ((pdCompletionUnit N p (j P.generator)).comp j))

/-- 導来テンソルから通常テンソルへの増大に沿う比較。高次 Tor の消滅を仮定しない。 -/
theorem lciCompletionH0Comparison (hf : IsKoszulRegularModGenerator P f)
    (h : IsDiscretePrismatic (E := E) P hP (lciQuotient P f)) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((prismCompleteInclusion (E := E) P).app _ (lciDerivedEnvelope (E := E) P f P₀ h₀ g hd))
      ((E.discrete A).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (lciCompletedOrdinary P f P₀ h₀ g hd)))) := by
  sorry -- lciDerivedEnvelope_eq_prismatic と h で B は離散。導来テンソル→N は非正で H⁰ 同型。
        -- derivedComplexCompletion_h0_map_isIso を p,d の順に適用して環の比較に移す

/-- BS 著者版 Example 7.9。導来完備テンソルの比較後に H⁰ と W₂ を使う。 -/
theorem lciDerivedEnvelope_isEnvelope_of_discrete (hf : IsKoszulRegularModGenerator P f)
    (hR : BoundedPTorsion p (lciQuotient P f)) (h : IsDiscretePrismatic (E := E) P hP (lciQuotient P f)) :
    let R := lciQuotient P f
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((prismCompleteInclusion (E := E) P).app _ (lciDerivedEnvelope (E := E) P f P₀ h₀ g hd))
      ((E.discrete A).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (discreteDeltaAlgebra (E := E) P hP R)))) ∧
      ∃ t : InitialDelta (E := E) P hP R h, IsLciEnvelope P f (discretePrism (E := E) P hP R h t.D t.base) (discreteBase (E := E) P hP R) := by
  sorry -- lciDerivedEnvelope_eq_prismatic と discreteDeltaIso。E⊗^L_U A→E⊗_U A の H⁰ 同型は
        -- derivedComplexCompletion_h0_map_isIso を p,d に適用して保たれる。lciTensorDelta と
        -- existsUnique_deltaPDCompletionHom から全 prism への一意な δ 射、有界性は HT と hR

/-- 普遍変数の δ 除算 E→H⁰Δ の mod d。比較の向きと f/d の像は envelope の普遍性で固定する。 -/
def universalModDComparison (r : ℕ)
    (hU : IsBoundedPrism (universalLciPrism P₀ h₀ r))
    (h : IsDiscretePrismatic (E := E) (universalLciPrism P₀ h₀ r) hU
      (lciQuotient (universalLciPrism P₀ h₀ r) (universalLciVariable P₀ r)))
    (D : DeltaStructure p (discretePrismaticRing (E := E) _ hU _ h))
    (hD : (universalLciPrism P₀ h₀ r).deltaStructure.IsDeltaHom D (discreteBase (E := E) _ hU _)) :
    let U := universalLciPrism P₀ h₀ r
    let R := lciQuotient U (universalLciVariable P₀ r)
    let datum := universalEnvelope P₀ h₀ r
    datum.ring ⧸ datum.Q.ideal →+* discretePrismaticRing (E := E) U hU R h ⧸ (discretePrism (E := E) U hU R h D hD).ideal := by
  let U := universalLciPrism P₀ h₀ r
  let R := lciQuotient U (universalLciVariable P₀ r)
  let datum := universalEnvelope P₀ h₀ r
  let Q := discretePrism (E := E) U hU R h D hD
  have lift := datum.envelope.lift Q (discreteBase (E := E) U hU R) hD
    (by
      apply Ideal.span_le.mpr
      rintro x (rfl : x = P₀.generator)
      change discreteBase (E := E) U hU R
        (completedFreeDeltaBase P₀ (ULift.{u} (Fin r)) P₀.generator) ∈ Q.ideal
      exact Ideal.mem_span_singleton_self _)
    (by sorry) -- HT 単位の構造三角から各 f_i は mod d で零
  exact Ideal.quotientMap Q.ideal lift.exists.choose (by
    rw [datum.envelope.ideal_eq]
    apply Ideal.span_le.mpr
    rintro x (rfl : x = datum.η (completedFreeDeltaBase P₀ (ULift.{u} (Fin r)) P₀.generator))
    change lift.exists.choose (datum.η (completedFreeDeltaBase P₀ (ULift.{u} (Fin r)) P₀.generator)) ∈ Q.ideal
    rw [show lift.exists.choose (datum.η (completedFreeDeltaBase P₀ (ULift.{u} (Fin r)) P₀.generator)) =
      discreteBase (E := E) U hU R (completedFreeDeltaBase P₀ (ULift.{u} (Fin r)) P₀.generator) from
        RingHom.congr_fun lift.exists.choose_spec.2 _]
    exact Ideal.mem_span_singleton_self _)

/-- G-A3-7。p ねじれなしの普遍例。Banach 代数の生成の計算は証明予定。 -/
theorem lci_envelope_surjective_invert_p_universal (r : ℕ)
    (hU : IsBoundedPrism (universalLciPrism P₀ h₀ r))
    (h : IsDiscretePrismatic (E := E) (universalLciPrism P₀ h₀ r) hU
      (lciQuotient (universalLciPrism P₀ h₀ r) (universalLciVariable P₀ r)))
    (hpU : NoPTorsion p (universalLciPrismRing P₀ r ⧸ (universalLciPrism P₀ h₀ r).ideal))
    (hpR : NoPTorsion p (lciQuotient (universalLciPrism P₀ h₀ r) (universalLciVariable P₀ r)))
    (D : DeltaStructure p (discretePrismaticRing (E := E) _ hU _ h))
    (hD : (universalLciPrism P₀ h₀ r).deltaStructure.IsDeltaHom D (discreteBase (E := E) _ hU _))
    (hφ : D.frobeniusLift = discretePrismaticFrobenius (E := E) _ hU _ h) :
    let q := universalModDComparison (E := E) P₀ h₀ r hU h D hD
    Function.Surjective (Localization.awayMap q (p : _)) := by
  sorry -- bar/Koszul 計算で f_i/d が gr¹ の基底 f_i mod J² に写る。p 反転後に生成する
        -- 稠密な部分代数を含み、retraction で像が閉。Bha12 Claim 3.30 の変種をここで証明する

include P₀ h₀ g hd in
/-- Ex 7.9。A 代数としての H⁰Δ とその構造射を envelope として特徴付ける。
この包からの一意な射で、有界な site の全対象に対する始性を得る。 -/
theorem prismaticCohomology_lci_eq_envelope (hf : IsKoszulRegularModGenerator P f)
    (hR : BoundedPTorsion p (lciQuotient P f)) :
    let R := lciQuotient P f
    let h := lci_isDiscretePrismatic (E := E) P hP f hf hR
    ∃ t : InitialDelta (E := E) P hP R h, IsLciEnvelope P f (discretePrism (E := E) P hP R h t.D t.base) (discreteBase (E := E) P hP R) := by
  have hc := lciDerivedEnvelope_isEnvelope_of_discrete (E := E) P hP f P₀ h₀ g hd hf hR
    (lci_isDiscretePrismatic (E := E) P hP f hf hR)
  exact hc.2

/-- 概要：R = A/(d,f) の p 冪ねじれが有界なら、正則列に対する prismatic envelope が存在する。
方針：自由変数の包絡を分類射で移し、有界ねじれを使って完備底変換の離散性を得る。
規約：BS 著者版 Example 7.9、D76。R は有界。普遍性の標的である任意の有界 prism 上の対象には追加の条件を課さない。
使われ方：lci 商の包絡の存在と、その有界な site の始性。 -/
theorem exists_lciEnvelope (hf : IsKoszulRegularModGenerator P f)
    (hR : BoundedPTorsion p (lciQuotient P f)) :
    ∃ (B : CommRingCat.{u}) (Q : OrientedPrism p B) (η : A →+* B), IsLciEnvelope P f Q η := by
  sorry -- 普遍変数の包絡の完備底変換。hR と completedBaseChange_bounded_torsion_pure を使う。

end Lci

/-! ## quasiregular semiperfectoid 環と Prop 7.10 -/

section Quasiregular

abbrev PadicBase (p : ℕ) [Fact p.Prime] := ULift.{u} (PadicInt p)

/-- 導来 p 完備な離散環の標準 ℤ_p 作用。 -/
def padicBaseAlgebra (S : Type u) [CommRing S]
    (h : IsModuleComplete S (p : S) (ModuleCat.of S S)) : Algebra (PadicBase.{u} p) S := by
  exact ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.arcPadicIntMap p S h).comp
    (ULift.ringEquiv : PadicBase.{u} p ≃+* PadicInt p).toRingHom).toAlgebra

/-- BS 著者版 §7.2 の quasiregular 条件。L̂_{S/ℤ_p}[−1] の導来 mod p が次数零の平坦な S/p 加群。 -/
def CotangentPCompletelyFlat (S : Type u) [CommRing S]
    (h : IsModuleComplete S (p : S) (ModuleCat.of S S)) : Prop :=
  letI := padicBaseAlgebra (p := p) S h
  let M := (cotangentWedgeAtAlgebra (E := E) p (PadicBase.{u} p) S 1).1
  let I : Ideal S := Ideal.span {(p : S)}
  let X := (completeDInclusion p S ≫ formShift S 1 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange (Ideal.Quotient.mk I)).app _ M
  ∃ N : ModuleCat.{u} (S ⧸ I), Module.Flat (S ⧸ I) N ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso X (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.moduleHeartVertex _ N))

/-- BS 著者版 §7.2 の quasiregular semiperfectoid 条件。
p 完備性、perfectoid の全射被覆、有界ねじれと、完備余接複体の平坦性を区別して保持する。 -/
structure IsQuasiregularSemiperfectoid (S : Type u) [CommRing S] : Prop where
  pComplete : IsModuleComplete S (p : S) (ModuleCat.of S S)
  semiperfectoid : ∃ (T : CommRingCat.{u}) (q : T →+* S), IsIntegralPerfectoid T p ∧ Function.Surjective q
  boundedTorsion : BoundedPTorsion p S
  cotangent_flat : CotangentPCompletelyFlat (E := E) (p := p) S pComplete

variable (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-- BS 著者版 Proposition 7.10 の固定した A_inf の係数環。本体を使う。 -/
abbrev ainfCoefficients (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] : CommRingCat.{u} :=
  Semiperfectoid.ainfClassicalCoefficients p R

/-- BS 著者版 Proposition 7.10 の A_inf の台環。本体と同じ固定した係数を使う。 -/
abbrev ainfPrismRing := (ainfCoefficients p R : Type u)

/-- Proposition 7.10の固定したFontaine射。 -/
abbrev ainfTheta (hR : IsIntegralPerfectoid R p) : ainfPrismRing (p := p) R →+* R :=
  Semiperfectoid.ainfClassicalTheta p R hR

/-- Proposition 7.10の標準δ構造。 -/
abbrev ainfDelta (hR : IsIntegralPerfectoid R p) : DeltaStructure p (ainfPrismRing (p := p) R) :=
  Semiperfectoid.ainfClassicalDelta p R hR

structure AinfData where
  prism : OrientedPrism p (ainfPrismRing (p := p) R)
  delta_eq : prism.deltaStructure = ainfDelta R hR
  perfect : prism.deltaStructure.IsPerfect
  bounded : IsBoundedPrism prism
  residue : ainfPrismRing (p := p) R ⧸ prism.ideal ≃+* R
  theta_eq : residue.toRingHom.comp (Ideal.Quotient.mk prism.ideal) = ainfTheta R hR

/-- Proposition 7.10のA_infのデータを本体の構成とその法則から読む。
係数環・δ・θはすべて固定したもの。別のprismを仮定しない。 -/
def ainfData : AinfData R hR where
  prism := Semiperfectoid.ainfClassicalPrism p R hR
  delta_eq := Semiperfectoid.ainfClassicalPrism_delta p R hR
  perfect := Semiperfectoid.ainfClassicalPrism_perfect p R hR
  bounded := Semiperfectoid.ainfClassicalPrism_bounded p R hR
  residue := Semiperfectoid.ainfClassicalResidueEquiv p R hR
  theta_eq := Semiperfectoid.ainfClassicalResidueEquiv_theta p R hR

/-- BS 著者版 Proposition 7.10 の固定した A_inf の prism。本体から得たデータの prism を取る。 -/
abbrev ainfPrism := (ainfData R hR).prism
variable (S : Type u) [CommRing S] [Algebra R S]

/-- R 代数を A_inf(R)/d 代数として読む。 -/
def ainfResidueAlgebra : Algebra (ainfPrismRing (p := p) R ⧸ (ainfPrism R hR).ideal) S :=
  ((algebraMap R S).comp (ainfData R hR).residue.toRingHom).toAlgebra

local instance : Algebra (ainfPrismRing (p := p) R ⧸ (ainfPrism R hR).ideal) S := ainfResidueAlgebra R hR S

abbrev QrspDiscrete := IsDiscretePrismatic (E := E) (ainfPrism R hR) (ainfData R hR).bounded S

/-- Prop 7.10(a)。一般の qrsp の有界ねじれを使い、完備余極限後の Δ̄ の離散性を示す。 -/
theorem qrsp_isDiscretePrismatic (hS : IsQuasiregularSemiperfectoid (E := E) (p := p) S) :
    QrspDiscrete (E := E) R hR S := by
  apply isDiscretePrismatic_of_hodgeTate (E := E)
  sorry -- 推移三角と décalage で各 gr が p 完全平坦。hS.boundedTorsion と完備余極限で HT が離散

/-- HT の単位 S→H⁰(Δ̄)=H⁰(Δ)/d。δ 構造を選ぶ前に使える。 -/
def qrspHTMap (h : QrspDiscrete (E := E) R hR S) :
    let P := ainfPrism R hR
    let C := discreteDeltaAlgebra (E := E) P (ainfData R hR).bounded S
    S →+* C.right ⧸ Ideal.span {C.hom.hom P.generator} :=
  (discreteHTArrow (E := E) (ainfPrism R hR) (ainfData R hR).bounded S h).val.right.hom

/-- Prop 7.10(a) の平坦性は S 上で測り、その S 作用には HT 単位を使う。 -/
theorem qrsp_completelyFaithfullyFlat (hS : IsQuasiregularSemiperfectoid (E := E) (p := p) S) :
    let P := ainfPrism R hR
    let C := discreteDeltaAlgebra (E := E) P (ainfData R hR).bounded S
    letI := (qrspHTMap (E := E) R hR S (qrsp_isDiscretePrismatic (E := E) R hR S hS)).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : S)}) (C.right ⧸ Ideal.span {C.hom.hom P.generator}) := by
  sorry -- mod p で各 gr は平坦、Fil₀ は S/p。平坦な余核による Fil₀ の純粋な包含と完備余極限を使う

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
  simpa only [rootBase, rootPolynomials, completionRing, Semiperfectoid.rootFamilyBase,
    Semiperfectoid.rootFamilyRaw] using
    (Semiperfectoid.rootFamilyBase_isIntegralPerfectoid p R J hR)

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
  exact (_root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift_to_bounded (ainfPrism R hR) (ainfData R hR).perfect
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
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (perfectBaseComparison (E := E) _ (ainfData R hR).bounded P' (ainfData R' h').bounded u)
      ((discreteToAnimated _).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex t))) ∧
      (letI : Algebra (ainfPrismRing (p := p) R' ⧸ P'.ideal) T := t.hom.hom.toAlgebra
       ∃ (w : Fin r → ainfPrismRing (p := p) R') (h : IsDiscretePrismatic (E := E) P' (ainfData R' h').bounded T)
         (t₀ : InitialDelta (E := E) P' (ainfData R' h').bounded T h),
         (∀ i, ainfTheta R' h' (w i) = rootX (p := p) R (ULift.up i : ULift.{u} (Fin r)) 0 - algebraMap R R' (f i)) ∧
           IsLciEnvelope P' w (discretePrism (E := E) P' (ainfData R' h').bounded T h t₀.D t₀.base)
             (discreteBase (E := E) P' (ainfData R' h').bounded T)) ∧
      ∃ h : QrspDiscrete (E := E) R hR T, Nonempty (InitialDelta (E := E) (ainfPrism R hR) (ainfData R hR).bounded T h) := by
  sorry -- T は R′ の X_i−f_i による Koszul 正則商。A′ で Ex 7.9、A へは
        -- perfectBaseComparison_isIso（(4) と乗法）。Lemma 4.8 の一意持ち上げで始性を移す

/-- 原典 Prop 7.10(b) の一般形の記録（W9-I-43、別単位）。E3 に使うのは下の T・S′ の始性。 -/
theorem qrsp_initial (hS : IsQuasiregularSemiperfectoid (E := E) (p := p) S) :
    Nonempty (InitialDelta (E := E) (ainfPrism R hR) (ainfData R hR).bounded S (qrsp_isDiscretePrismatic (E := E) R hR S hS)) := by
  sorry -- 別単位：一般の qrsp には原典の自然な δ 自己準同型の議論が必要。T の帰着のみでは示さない

/-- 完全化の台と構造射。理想の生成元は完全化単位で送った d。 -/
def perfectedCoefficients {B : Type u} [CommRing B] (Q : OrientedPrism p B) : CommRingCat.{u} := by
  let datum := Q.deltaStructure
  let b := deltaPerfectionOf datum 0 Q.generator
  letI := pdCompletionCommRing (DeltaPerfection datum) p b
  exact CommRingCat.of (PDCompletionH0 (DeltaPerfection datum) p b)

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
    OrientedPrism.Hom Q (perfectedPrism Q) := by
  letI := pdCompletionCommRing (DeltaPerfection Q.deltaStructure) p
    (deltaPerfectionOf Q.deltaStructure 0 Q.generator)
  let j := (pdCompletionUnit (DeltaPerfection Q.deltaStructure) p
    (deltaPerfectionOf Q.deltaStructure 0 Q.generator)).comp (deltaPerfectionOf Q.deltaStructure 0)
  have hg : j Q.generator = (perfectedPrism Q).generator := by
    rw [perfectedPrism, perfectDeltaPDPrism_generator]
    rfl
  refine { toRingHom := j
           map_delta := (pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom _ 0)
           ideal_le := ?_ }
  apply Ideal.span_le.mpr
  rintro x (rfl : x = Q.generator)
  change j Q.generator ∈ Ideal.span {(perfectedPrism Q).generator}
  rw [hg]
  exact Ideal.mem_span_singleton_self _

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
    ∃ h : QrspDiscrete (E := E) R hR S', Nonempty (InitialDelta (E := E) (ainfPrism R hR) (ainfData R hR).bounded S' h) := by
  sorry -- 有限部分集合の regularSemiperfectoid_prismatic、Δ の完備 filtered 余極限保存。
        -- δ 射の両立族を完備化へ延長して始性を得る（一般 qrsp の始性は使わない）

/-- W9-I-43・44。有限部分族の始性を完備 filtered 余極限へ移し、S′ の上で比較する。 -/
theorem rootQuotient_prismatic_perfection_eq (J : Type u) :
    let R' := rootBase (p := p) R J
    let S' := rootQuotient (p := p) R (fun _ : J => 0)
    let h' := rootBase_perfectoid R hR J
    let P' := ainfPrism R' h'
    let r := (rootQuotientMap (p := p) R (fun _ : J => 0)).comp (ainfTheta R' h')
    ∃ (h : QrspDiscrete (E := E) R hR S') (d : InitialDelta (E := E) (ainfPrism R hR) (ainfData R hR).bounded S' h)
      (hr : Function.Surjective r),
      let Q := discretePrism (E := E) (ainfPrism R hR) (ainfData R hR).bounded S' h d.D d.base
      let η := (toPerfectedPrism Q).quotientMap.comp
        (discreteHTMap (E := E) (ainfPrism R hR) (ainfData R hR).bounded S' h d.D d.base)
      r P'.generator = 0 ∧ IsPerfectoidization p η ∧
        ((Subsingleton R' ∧ Subsingleton S' ∧ Subsingleton (perfectedCoefficients Q ⧸ (perfectedPrism Q).ideal)) ∨
          (Nontrivial R' ∧ ¬IsUnit (p : ainfPrismRing (p := p) R' ⧸ P'.ideal) ∧
            IsCor73Comparison P' (ainfData R' h').perfect r hr (perfectedPrism Q) η)) := by
  obtain ⟨h, ⟨d⟩⟩ := rootQuotient_initial (E := E) R hR J
  refine ⟨h, d, ?_, ?_⟩
  · sorry -- R′ 完備なので商の p 完備化への射は全射。θ の全射性と合成
  · sorry -- existsUnique_deltaPerfectionPDCompletionHom で完全標的への始性に移す。
        -- r=θ の後に商と完備化。R′≠0 では剰余環の p は非単元で Cor 7.3 の入口に
        -- exists_perfectoidization_of_perfectPrism_quotient に hr と r(d′)=0 を渡す。
        -- 両普遍性と Lemma 4.8 で S′ 上の完全 prism の唯一の同型。R′=0 では全て零環

end Quasiregular

variable {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)

/-- BS 著者版 Example 7.9 の普遍向き付き基底への特殊化。
一般のlci比較に既存の普遍prismの射を代入する。 -/
theorem prismaticCohomology_lci_universal {r : ℕ} (f : Fin r → A)
    (hf : IsKoszulRegularModGenerator P f) (hb : BoundedPTorsion p (lciQuotient P f)) :
    let R := lciQuotient P f
    let h := lci_isDiscretePrismatic (E := E) P hP f hf hb
    ∃ t : InitialDelta (E := E) P hP R h, IsLciEnvelope P f (discretePrism (E := E) P hP R h t.D t.base) (discreteBase (E := E) P hP R) := by
  obtain ⟨g, hg, _⟩ := universalOrientedPrism_hom P
  exact prismaticCohomology_lci_eq_envelope (E := E) P hP f (universalOrientedPrism.{u} (p := p)) (universalOrientedPrism_bounded (p := p)) g hg hf hb


end SerrePositivity.BhattScholze.Prismatic
