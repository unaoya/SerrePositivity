module


public meta import SerrePositivity.Util.Citation
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Site.ArcCardinality
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Valuations.ArcValuationExtension
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.Surjectivity
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra

/-!
# p 完備環の affine arc site

## 概要
濃度を制限した導来 p 完備環の小さい模型に、有限 arc 被覆族の生成する位相を入れる
（BS 著者版 Definition 8.7 の affine 版）。整 perfectoid 環が cover-dense であることを示す
（同 Lemma 8.8 の affine 版）。

## 方針
被覆の底変換と合成は試験付値環への持ち上げから示す。
有限積から整域への射は一因子を通る。
一点の perfectoid 被覆は完備底変換、根添加、Fontaine 写像から得る半 perfectoid 商の
普遍 perfectoid 化を使って構成する。

## 規約
試験付値環は階数 1 で古典的 p 完備。試験環の拡大には忠実平坦性を要求する。
位相は環の圏の opposite に置く。

## 使われ方
整 perfectoid 環の充満部分圏への層の制限と、BS 著者版 Proposition 8.10 の arc 降下。
-/

@[expose] public noncomputable section

universe u
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Cardinal
open scoped _root_.TensorProduct _root_.Cardinal

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface _root_.SerrePositivity.DerivedCompletion

variable (p : ℕ) [Fact p.Prime] (κ : Cardinal.{u})

/-! ## 台の圏 -/

/-- 導来 p 完備性と濃度を併記する、環の圏上の対象条件。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affComplProperty : ObjectProperty CommRingCat.{u} := fun S =>
  IsModuleComplete S (p : S) (ModuleCat.of S S) ∧ Cardinal.mk S ≤ κ

/-- 小さい模型を取る前の充満部分圏。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffComplLarge := (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affComplProperty p κ).FullSubcategory

omit [Fact p.Prime] in
private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.complete_of_ringEquiv {R T : Type u} [CommRing R] [CommRing T]
    (e : R ≃+* T) (hR : IsModuleComplete R (p : R) (ModuleCat.of R R)) :
    IsModuleComplete T (p : T) (ModuleCat.of T T) := by
  let A := e.symm.toRingHom.toAlgebra
  let : Algebra T R := A
  have h := complete_along_map p (CommRingCat.ofHom e.symm.toRingHom) hR
  let E : T ≃ₗ[T] R := by
    refine { (e.symm.toAddEquiv) with map_smul' := ?_ }
    intro a b
    change e.symm (a * b) = e.symm a * e.symm b
    exact map_mul _ _ _
  exact isModuleComplete_of_linearEquiv T (p : T) (ModuleCat.of T R) _ E.symm h

instance _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affComplLarge_essentiallySmall : EssentiallySmall.{u} (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffComplLarge p κ) := by
  classical
  let K := κ.out
  let Codes : Type u :=
    {x : (Σ s : Set K, CommRing s) // _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affComplProperty p κ (@CommRingCat.of x.1 x.2)}
  let f : Codes → Skeleton (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffComplLarge p κ) := fun x =>
    toSkeleton (⟨@CommRingCat.of x.val.1 x.val.2, x.property⟩ : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffComplLarge p κ)
  apply (essentiallySmall_iff _).mpr
  refine ⟨small_of_surjective (f := f) ?_, inferInstance⟩
  intro q
  obtain ⟨X, rfl⟩ := Quotient.exists_rep q
  obtain ⟨emb⟩ := (Cardinal.le_def X.obj K).mp (X.property.2.trans_eq (Cardinal.mk_out κ).symm)
  let E := Equiv.ofInjective emb emb.injective
  let r : CommRing (Set.range emb) := E.symm.commRing
  let : CommRing (Set.range emb) := r
  let e : X.obj ≃+* Set.range emb := (E.symm.ringEquiv).symm
  have hp : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affComplProperty p κ (CommRingCat.of (Set.range emb)) :=
    ⟨_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.complete_of_ringEquiv p e X.property.1, (Cardinal.mk_congr E).symm.trans_le X.property.2⟩
  refine ⟨⟨⟨Set.range emb, r⟩, hp⟩, ?_⟩
  exact congr_toSkeleton_of_iso ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affComplProperty p κ).isoMk e.toCommRingCatIso).symm

/-- 概要：κ-small の p 完備環の圏（affine の p 進形式スキーム）。
方針：導来 p 完備性と濃度 ≤ κ を満たす `CommRingCat.{u}` の充満部分圏の `SmallModel`。
規約：対象の濃度 ≤ κ。
使われ方：arc site の台。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffCompl : Type u := SmallModel (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffComplLarge p κ)

instance : Category.{u} (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffCompl p κ) := inferInstance

/-- 小さい模型から元の環への忘却。射の環準同型もこの関手で取り出す。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affComplForget : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffCompl p κ ⥤ CommRingCat.{u} :=
  (equivSmallModel (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffComplLarge p κ)).inverse ⋙ (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affComplProperty p κ).ι

/-- 小さい p 完備環の圏内での perfectoid 条件。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affPerfdProperty : ObjectProperty (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffCompl p κ) := fun S =>
  _root_.SerrePositivity.IsIntegralPerfectoid ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affComplForget p κ).obj S) p

/-- 概要：κ-small の perfectoid 環の充満部分圏 affPerfd_κ ⊂ affCompl_κ。
方針：`IsIntegralPerfectoid` の `ObjectProperty.FullSubcategory`。
規約：—
使われ方：Prop 8.10、F_T。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffPerfd : Type u := (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affPerfdProperty p κ).FullSubcategory

instance : Category.{u} (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffPerfd p κ) := inferInstance

/-- 概要：包含関手 affPerfd_κ ⥤ affCompl_κ（充満忠実）。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affPerfdInclusion : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffPerfd p κ ⥤ _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffCompl p κ :=
  (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affPerfdProperty p κ).ι

/-! ## arc 被覆と arc 位相 -/

/-- 概要：有限族 {R → R_i} が arc 被覆（[BM18, Def 1.2]、Def 8.7 の affine 版）。
方針：∀ V（`IsRankOneCompleteValuationRing`）、∀ R → V、∃ i W（同じ種類）、V → W 忠実平坦、∃ R_i → W、両立。
規約：族の添字は `Finite`。単射の場合は族 = 一点。
使われ方：`arcTopology`、Prop 8.10、Cor 8.12 の二つの被覆。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily {R : Type u} [CommRing R] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)]
    (f : ∀ i, R →+* B i) : Prop :=
  ∀ (V : Type u) [CommRing V], _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p V → ∀ k : R →+* V,
    ∃ (i : ι) (W : Type u) (_ : CommRing W), _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p W ∧
      ∃ (e : V →+* W), e.FaithfullyFlat ∧
        ∃ l : B i →+* W, l.comp (f i) = e.comp k

/-- 概要：arc 位相：有限 arc 被覆族の生成 sieve を含む Grothendieck 位相の sInf（A0 の `flatTopology` と同じ形）。
方針：`Sieve.generate (Presieve.ofArrows …)`。
規約：affCompl_κ の opposite の上。
使われ方：以下。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTopology : GrothendieckTopology (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffCompl p κ)ᵒᵖ :=
  sInf { J | ∀ (ι : Type u) [Finite ι] (R : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffCompl p κ)
    (B : ι → _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffCompl p κ) (f : ∀ i, R ⟶ B i),
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily p (fun i => (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affComplForget p κ).obj (B i))
      (fun i => ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affComplForget p κ).map (f i)).hom) →
    Sieve.generate (Presieve.ofArrows (fun i => Opposite.op (B i))
      (fun i => (f i).op)) ∈ J (Opposite.op R) }

/-- `affPerfd_κ` への誘導位相。包含の opposite に `Functor.inducedTopology` を使う。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTopologyPerfd : GrothendieckTopology (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffPerfd p κ)ᵒᵖ :=
  (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affPerfdInclusion p κ).op.inducedTopology (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTopology p κ)

/-! ## coverage -/

/-- 概要：arc 被覆族は底変換で安定：R → R′ と {R → R_i} に対し {R′ → R_i ⊗̂_R R′}（p 完備テンソル）も arc 被覆族。
方針：R′ → V は R → V を与え、持ち上げ R_i → W と R′ → V → W から R_i ⊗̂_R R′ → W（W は p 完備）。
規約：完備テンソルは `CompletedTensor`（perfectoid なら perfectoid）。
使われ方：生成系の補題（S1 `isSheaf_toGrothendieck_iff`）を使うための coverage 条件。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.isArcCoverFamily_baseChange (p : ℕ) [Fact p.Prime]
    {R R' : Type u} [CommRing R] [CommRing R']
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    (f : ∀ i, R →+* B i) (g : R →+* R')
    (_hR : IsModuleComplete R (p : R) (ModuleCat.of R R))
    (_hR' : IsModuleComplete R' (p : R') (ModuleCat.of R' R'))
    (_hB : ∀ i, IsModuleComplete (B i) (p : B i) (ModuleCat.of (B i) (B i)))
    (hf : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily p B f) :
    letI : Algebra R R' := g.toAlgebra
    letI : ∀ i, Algebra R (B i) := fun i => (f i).toAlgebra
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily p
      (fun i => completionRing p (CommRingCat.of (B i ⊗[R] R')))
      (fun i => (completionUnit p (CommRingCat.of (B i ⊗[R] R'))).hom.comp
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] B i ⊗[R] R').toRingHom) := by
  let : Algebra R R' := g.toAlgebra
  let : ∀ i, Algebra R (B i) := fun i => (f i).toAlgebra
  change _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily p _ _
  intro V _ hV k
  obtain ⟨i, W, hWring, hW, e, he, l, hl⟩ := hf V hV (k.comp g)
  let : CommRing W := hWring
  let : Algebra R W := (l.comp (f i)).toAlgebra
  let lₐ : B i →ₐ[R] W := { l with commutes' := fun _ => rfl }
  let kₐ : R' →ₐ[R] W :=
    { (e.comp k) with commutes' := fun a => (RingHom.congr_fun hl a).symm }
  let A := B i ⊗[R] R'
  have ht (x : B i) (y : R') : Commute (lₐ x) (kₐ y) := Commute.all _ _
  let t := Algebra.TensorProduct.lift lₐ kₐ ht
  let j : R' →ₐ[R] A := Algebra.TensorProduct.includeRight
  let τ := _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.completionLift p
    (CommRingCat.ofHom t.toRingHom) (hW.isModuleComplete p)
  refine ⟨i, W, hWring, hW, e, he, τ.hom, ?_⟩
  rw [← RingHom.comp_assoc]
  change ((completionUnit p (CommRingCat.of A) ≫ τ).hom).comp j.toRingHom = e.comp k
  rw [_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.completionLift_comp]
  exact congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeRight' lₐ kₐ ht)

/-- 概要：合成・有限族の合併・有限積への置き換え（{R → R_i} と R → ∏R_i は同じ位相を生成）。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.isArcCoverFamily_comp (p : ℕ) [Fact p.Prime]
    {R : Type u} [CommRing R] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, R →+* B i)
    (J : ι → Type u) [∀ i, Finite (J i)]
    (C : ∀ i, J i → Type u) [∀ i j, CommRing (C i j)]
    (g : ∀ i j, B i →+* C i j)
    (hf : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily p B f)
    (hg : ∀ i, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily p (C i) (g i)) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily p (fun ij : Sigma J => C ij.1 ij.2)
      (fun ij => (g ij.1 ij.2).comp (f ij.1)) := by
  intro V _ hV k
  obtain ⟨i, W, hWring, hW, e, he, l, hl⟩ := hf V hV k
  let : CommRing W := hWring
  obtain ⟨j, Z, hZring, hZ, d, hd, m, hm⟩ := hg i W hW l
  let : CommRing Z := hZring
  refine ⟨⟨i, j⟩, Z, hZring, hZ, d.comp e,
    RingHom.FaithfullyFlat.stableUnderComposition e d he hd, m, ?_⟩
  rw [← RingHom.comp_assoc, hm, RingHom.comp_assoc, hl, ← RingHom.comp_assoc]

theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.isArcCoverFamily_prod_iff (p : ℕ) [Fact p.Prime]
    {R : Type u} [CommRing R] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, R →+* B i) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily p B f ↔
      _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily p (fun _ : PUnit.{u + 1} => ∀ i, B i)
        (fun _ => RingHom.pi f) := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · intro h V _ hV k
    obtain ⟨i, W, hWring, hW, e, he, l, hl⟩ := h V hV k
    let : CommRing W := hWring
    exact ⟨PUnit.unit, W, hWring, hW, e, he, l.comp (Pi.evalRingHom B i), hl⟩
  · intro h V _ hV k
    obtain ⟨_, W, hWring, hW, e, he, l, hl⟩ := h V hV k
    let : CommRing W := hWring
    let : IsDomain W := hW.isDomain
    have hsum : (∑ i, Pi.single i (1 : B i)) = (1 : ∀ i, B i) := by
      ext i
      simp
    have hex : ∃ i, l (Pi.single i (1 : B i)) ≠ 0 := by
      by_contra! hz
      have heq := congrArg l hsum
      rw [map_sum, map_one] at heq
      simp only [hz, Finset.sum_const_zero] at heq
      exact zero_ne_one heq
    obtain ⟨i, hi⟩ := hex
    have hone : l (Pi.single i (1 : B i)) = 1 := by
      have hsq : l (Pi.single i (1 : B i)) * l (Pi.single i (1 : B i)) =
          l (Pi.single i (1 : B i)) := by
        rw [← map_mul]
        congr 1
        ext j
        by_cases hj : j = i
        · subst j
          simp
        · simp [Pi.single_eq_of_ne hj]
      exact mul_left_cancel₀ hi (hsq.trans (mul_one _).symm)
    let m : B i →+* W :=
      { toFun := fun a => l (Pi.single i a)
        map_one' := hone
        map_zero' := by simp
        map_add' := fun a b => by rw [Pi.single_add, map_add]
        map_mul' := fun a b => by rw [Pi.single_mul, map_mul] }
    have hm : m.comp (Pi.evalRingHom B i) = l := by
      apply RingHom.ext
      intro x
      change l (Pi.single i (x i)) = l x
      have hh : Pi.single i (x i) = Pi.single i (1 : B i) * x := by
        ext j
        by_cases hj : j = i
        · subst j
          simp
        · simp [Pi.single_eq_of_ne hj]
      rw [hh, map_mul, hone, one_mul]
    refine ⟨i, W, hWring, hW, e, he, m, ?_⟩
    change m.comp ((Pi.evalRingHom B i).comp (RingHom.pi f)) = _
    rw [← RingHom.comp_assoc, hm]
    exact hl

/-! ## Lemma 8.8 の affine 版 -/

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionUnit_modP_surjective (p : ℕ) (C : CommRingCat.{u}) :
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {(p : completionRing p C)})).comp
      (completionUnit p C).hom) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  let X := PrincipalCompletionH0 C (p : C)
  let : CommRing X := principalCompletionCommRing C (p : C)
  let j₀ : C →+* X := principalCompletionUnitRingHom C (p : C)
  let E : X ≃ₗ[C] PrincipalReflectionModule C (p : C) := principalCompletionH0Equiv C (p : C)
  obtain ⟨s, hs⟩ := (principalReflectionRelation C (p : C)).range.mkQ_surjective (E x)
  refine ⟨s 0, ?_⟩
  let j := (completionUnit p C).hom
  change Ideal.Quotient.mk _ (j (s 0)) = Ideal.Quotient.mk _ x
  symm
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨E.symm (principalReflectionMk C (p : C) (sequenceTail C s)), ?_⟩
  have hj : E (j (s 0)) = (s 0) • principalReflectionUnit C (p : C) := by
    change E (principalCompletionUnitRingHom C (p : C) (s 0)) = _
    rw [principalCompletionUnitRingHom_apply, principalCompletionH0Equiv_unit,
      principalReflectionUnit, ← map_smul]
    congr 1
    funext n
    cases n <;> simp [sequenceHead, smul_eq_mul]
  let y := E.symm (principalReflectionMk C (p : C) (sequenceTail C s))
  let y' : completionRing p C := y
  have hx' : (x : X) = j₀ (s 0) + (p : C) • y := by
    apply E.injective
    dsimp only [y]
    rw [map_add, map_smul, LinearEquiv.apply_symm_apply,
      show E (j₀ (s 0)) = _ from hj, ← hs]
    exact principalReflectionMk_decomposition C (p : C) s
  let t : X := (p : C) • y
  have hm : j (p : C) * y' = t :=
    (principalCompletionH0_isCompleteModuleReflection C (p : C)).mul_scalar_unit (p : C) y
  have hx : x = j (s 0) + j (p : C) * y' :=
    hx'.trans (congrArg (fun a : X => j₀ (s 0) + a) hm.symm)
  change x - j (s 0) = (p : completionRing p C) * y'
  rw [hx, map_natCast]
  abel

omit [Fact p.Prime] in
private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rootClosure_frobenius_surjective (R S : Type u) [CommRing R] [CommRing S] :
    Function.Surjective (fun x : ModP (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure p R S) p => x ^ p) := by
  let F := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S
  let C := colimit F
  let j := (completionUnit p C).hom
  let q : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure p R S →+* ModP (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure p R S) p := Ideal.Quotient.mk _
  intro z
  obtain ⟨c, rfl⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionUnit_modP_surjective p C z
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget CommRingCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨n, a, ha⟩ := Concrete.colimit_exists_rep F c
  let Q := MvPolynomial (F.obj n ⊕ F.obj n) (F.obj n) ⧸ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p (F.obj n)
  let m : MvPolynomial (F.obj n ⊕ F.obj n) (F.obj n) →+* Q := Ideal.Quotient.mk _
  let t := (completionUnit p (CommRingCat.of Q)).hom
  let f := (q.comp j).comp ((colimit.ι F (n + 1)).hom.comp (t.comp m))
  refine ⟨f (MvPolynomial.X (Sum.inl a)), ?_⟩
  have hzero : f (p : MvPolynomial (F.obj n ⊕ F.obj n) (F.obj n)) = 0 := by
    rw [map_natCast, ← map_natCast q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hrel : f (MvPolynomial.C a - MvPolynomial.X (Sum.inl a) ^ p -
      (p : MvPolynomial (F.obj n ⊕ F.obj n) (F.obj n)) * MvPolynomial.X (Sum.inr a)) = 0 := by
    let b := (q.comp j).comp ((colimit.ι F (n + 1)).hom.comp t)
    have h0 : m (MvPolynomial.C a - MvPolynomial.X (Sum.inl a) ^ p -
        (p : MvPolynomial (F.obj n ⊕ F.obj n) (F.obj n)) * MvPolynomial.X (Sum.inr a)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨a, rfl⟩)
    exact (congrArg b h0).trans (map_zero b)
  rw [map_sub, map_sub, map_pow, map_mul, hzero, zero_mul, sub_zero] at hrel
  have hmap : F.map (homOfLE (Nat.le_add_right n 1)) =
      CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStepUnit p R (F.obj n)) :=
    Functor.ofSequence_map_homOfLE_succ _ n
  have hn := colimit.w F (homOfLE (Nat.le_add_right n 1))
  rw [hmap] at hn
  have hn' := congrArg (fun k : F.obj n ⟶ C => q (j (k.hom a))) hn
  exact (sub_eq_zero.mp hrel).symm.trans (hn'.trans (congrArg (q.comp j) ha))

omit [Fact p.Prime] in
private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.modP_adicCompletion_surjective (A : Type u) [CommRing A] :
    let I : Ideal A := Ideal.span {(p : A)}
    let B := AdicCompletion I A
    Function.Surjective (_root_.SerrePositivity.modPMap p (algebraMap A B)) := by
  dsimp only
  let I : Ideal A := Ideal.span {(p : A)}
  let B := AdicCompletion I A
  let J : Ideal B := Ideal.span {(p : B)}
  have hJ : I.map (algebraMap A B) = J := by
    simp only [I, J, Ideal.map_span, Set.image_singleton, map_natCast]
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.exists_adicCompletion_algebraMap_sub_mem I (Submodule.fg_span_singleton _) 1 x
  refine ⟨Ideal.Quotient.mk I a, ?_⟩
  change Ideal.Quotient.mk J (algebraMap A B a) = Ideal.Quotient.mk J x
  apply Ideal.Quotient.eq.mpr
  have ha' : algebraMap A B a - x ∈ (I ^ 1).map (algebraMap A B) := ha
  rw [pow_one, hJ] at ha'
  exact ha'

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_perfectoid_surjection_of_classical_complete {R A : Type u}
    [CommRing R] [CommRing A] [IsAdicComplete (Ideal.span {(p : A)}) A]
    (f : R →+* A) (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p)
    (hF : Function.Surjective (fun x : ModP A p => x ^ p)) :
    ∃ (T : Type u) (_ : CommRing T) (q : T →+* A),
      _root_.SerrePositivity.IsIntegralPerfectoid T p ∧ Function.Surjective q := by
  by_cases hA : Subsingleton A
  · exact ⟨A, inferInstance, RingHom.id _, Or.inl hA, Function.surjective_id⟩
  have hpA : ¬ IsUnit (p : A) := fun h => hA (_root_.SerrePositivity.subsingleton_of_isUnit_natCast_of_isHausdorff p A h)
  let : Fact (¬ IsUnit (p : A)) := ⟨hpA⟩
  rcases hR with hR | ⟨hpR, hcR, ⟨π, uπ, hπ⟩, hFR, hker⟩
  · let := hR
    exact (hA f.codomain_trivial).elim
  let : Fact (¬ IsUnit (p : R)) := ⟨hpR⟩
  let := hcR
  obtain ⟨d, hd, hdker⟩ := _root_.SerrePositivity.BhattScholze.exists_distinguished_fontaine_kernel_generator R p hFR hker π uπ hπ
  let L : PreTilt R p →+* PreTilt A p := Perfection.map p (_root_.SerrePositivity.modPMap p f)
  let d' : WittVector p (PreTilt A p) := WittVector.map L d
  have hd' : (_root_.SerrePositivity.BhattScholze.wittDeltaStructure p (PreTilt A p)).IsDistinguished d' :=
    (_root_.SerrePositivity.BhattScholze.wittDeltaStructure_isDistinguished_iff p _ _).mpr
      (((_root_.SerrePositivity.BhattScholze.wittDeltaStructure_isDistinguished_iff p _ _).mp hd).map L)
  let θ := WittVector.fontaineTheta A p
  have hd0 : WittVector.fontaineTheta R p d = 0 :=
    show d ∈ RingHom.ker (WittVector.fontaineTheta R p) from
      hdker ▸ Ideal.mem_span_singleton_self _
  have hz : θ d' = 0 := by
    rw [show θ d' = f (WittVector.fontaineTheta R p d) from
      RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.fontaineTheta_natural p f) d, hd0, map_zero]
  let K := PreTilt A p
  let W := WittVector p K
  let D := _root_.SerrePositivity.BhattScholze.wittDeltaStructure p K
  let hD := _root_.SerrePositivity.BhattScholze.wittDeltaStructure_isPerfect p K
  let : CommRing (PDCompletionH0 W p d') := pdCompletionCommRing W p d'
  let P := _root_.SerrePositivity.BhattScholze.perfectDeltaPDPrism D hD d' hd'
  have hP := _root_.SerrePositivity.BhattScholze.perfectDeltaPDPrism_isPerfect D hD d' hd'
  have hAc := isModuleComplete_of_isAdicComplete A (p : A) (ModuleCat.of A A)
  have hAd : IsModuleComplete A (θ d') (ModuleCat.of A A) := by
    rw [hz]
    exact isModuleComplete_of_pow_smul_zero A 0 _ 1 (by simp)
  obtain ⟨g, hg, _⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_pdCompletionRingHom W p d' A θ hAc hAd
  let q := Ideal.Quotient.lift P.ideal g (by
    change Ideal.span {pdCompletionUnit W p d' d'} ≤ RingHom.ker g
    exact (Ideal.span_singleton_le_iff_mem _).mpr ((RingHom.congr_fun hg d').trans hz))
  refine ⟨_, inferInstance, q, P.quotient_isIntegralPerfectoid hP, ?_⟩
  intro a
  obtain ⟨x, hx⟩ := surjective_fontaineTheta hF a
  exact ⟨Ideal.Quotient.mk _ (pdCompletionUnit W p d' x), (RingHom.congr_fun hg x).trans hx⟩


private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.adicCompletion_cardinal_le {A : Type u} [CommRing A] (I : Ideal A) :
    #(AdicCompletion I A) ≤ #A ^ ℵ₀ := by
  classical
  let s (n : ℕ) : A ⧸ I ^ n → A := Function.surjInv Ideal.Quotient.mk_surjective
  let f : AdicCompletion I A → ℕ → A := fun x n => s n (AdicCompletion.evalₐ I n x)
  have hf : Function.Injective f := by
    intro x y h
    apply AdicCompletion.ext_evalₐ
    intro n
    have hn := congrArg (Ideal.Quotient.mk (I ^ n)) (congrFun h n)
    simpa only [f, s, Function.surjInv_eq] using hn
  exact (Cardinal.mk_le_of_injective hf).trans_eq (by simp)

/-- BS 著者版 Lemma 8.8 の affine 版。所定の濃度以下の整 perfectoid 環による一点被覆。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_perfectoid_arcCover (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    ∃ (T : CommRingCat.{u}) (g : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension p S hS →+* T),
      _root_.SerrePositivity.IsIntegralPerfectoid T p ∧
      Cardinal.mk T ≤ (Cardinal.mk S + Cardinal.aleph0) ^ Cardinal.aleph0 ∧
      _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily p (fun _ : PUnit.{u + 1} => (T : Type u))
        (fun _ => g.comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtensionUnit p S hS)) := by
  let R := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p
  let S₀ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension p S hS
  let B := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure p R S₀
  let uB := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureUnit p R S₀
  let I : Ideal B := Ideal.span {(p : B)}
  let A := AdicCompletion I B
  let j := algebraMap B A
  have hI : I.FG := Submodule.fg_span_singleton _
  have hmap : I.map j = Ideal.span {(p : A)} := by
    simp only [I, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x : A => Ideal.span {x}) (map_natCast j p)
  let : IsAdicComplete (Ideal.span {(p : A)}) A :=
    hmap ▸ AdicCompletion.isAdicComplete_self I hI
  have hA : IsModuleComplete A (p : A) (ModuleCat.of A A) :=
    isModuleComplete_of_isAdicComplete A (p : A) _
  have hF : Function.Surjective (fun x : ModP A p => x ^ p) := by
    intro x
    obtain ⟨b, rfl⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.modP_adicCompletion_surjective p B x
    obtain ⟨c, hc⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rootClosure_frobenius_surjective p R S₀ b
    exact ⟨_root_.SerrePositivity.modPMap p j c, (map_pow _ _ _).symm.trans (congrArg (_root_.SerrePositivity.modPMap p j) hc)⟩
  obtain ⟨P, hPring, q, hP, hq⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_perfectoid_surjection_of_classical_complete p
    (j.comp (algebraMap R B)) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing_isPerfectoid p) hF
  let : CommRing P := hPring
  obtain ⟨T, hTring, uT, hT, huT⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_surjective_perfectoidization_of_semiperfectoid_quotient
    hP q hq hA
  let : CommRing T := hTring
  let g := uT.comp (j.comp uB)
  have hbound : #T ≤ (#S + ℵ₀) ^ ℵ₀ := by
    let c := #S + ℵ₀
    let κ := c ^ ℵ₀
    have hκ : ℵ₀ ≤ κ := le_add_self.trans (Cardinal.self_le_power c one_le_aleph0)
    have hκpow : κ ^ ℵ₀ = κ := by
      dsimp only [κ]
      rw [← Cardinal.power_mul, Cardinal.mul_eq_self le_rfl]
    have hS₀ : #S₀ ≤ κ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension_cardinal_le p S hS
    have hB : #B ≤ κ := (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rootClosure_cardinal_le p R S₀).trans (by
      have hsum : #S₀ + ℵ₀ ≤ κ := (add_le_add hS₀ hκ).trans_eq (by
        rw [Cardinal.add_eq_max hκ, max_self])
      exact (Cardinal.power_le_power_right hsum).trans_eq hκpow)
    exact (Cardinal.mk_le_of_surjective huT).trans ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.adicCompletion_cardinal_le I).trans
      ((Cardinal.power_le_power_right hB).trans_eq hκpow))
  refine ⟨CommRingCat.of T, g, hT.1, hbound, ?_⟩
  intro V _ hV k
  obtain ⟨W, e, l, hW, hWperf, he, hl⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_baseExtension_lift p S hS (CommRingCat.of V) hV k
  obtain ⟨m, hm⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure_extends p R S₀ W hWperf l
  let : Algebra B W := m.toAlgebra
  let : IsAdicComplete I W := (IsAdicComplete.map_algebraMap_iff I W).mp (by
    rw [show I.map (algebraMap B W) = Ideal.span {(p : W)} from by
      simp only [I, Ideal.map_span, Set.image_singleton]
      exact congrArg (fun x : W => Ideal.span {x}) (map_natCast (algebraMap B W) p)]
    exact hW.adicComplete)
  let r : A →ₐ[B] W := _root_.SerrePositivity.adicCompletionToCompleteAlgebra B I hI W
  obtain ⟨n, hn, _⟩ := hT.2 W hWperf r.toRingHom
  refine ⟨PUnit.unit, W, inferInstance, hW, e, he, n, ?_⟩
  have hr : r.toRingHom.comp j = m := RingHom.ext r.commutes
  calc
    n.comp (g.comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtensionUnit p S hS)) =
        ((n.comp uT).comp (j.comp uB)).comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtensionUnit p S hS) := by
      simp only [g, RingHom.comp_assoc]
    _ = (m.comp uB).comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtensionUnit p S hS) := by
      rw [hn, ← RingHom.comp_assoc uB j r.toRingHom, hr]
    _ = e.comp k := by rw [hm, hl]

/-- 濃度上界を保つ affine arc site では整 perfectoid 環が cover-dense。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affPerfdInclusion_isCoverDense (κ : Cardinal.{u})
    [hκ : Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)] :
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affPerfdInclusion p κ).op.IsCoverDense (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTopology p κ) := by
  apply Functor.isCoverDense_of_generate_singleton_functor_π_mem
  intro X
  let E := equivSmallModel (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffComplLarge p κ)
  let F := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affComplForget p κ
  let : F.Full := by
    change (E.inverse ⋙ (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affComplProperty p κ).ι).Full
    infer_instance
  let R := F.obj X.unop
  have hR : IsModuleComplete R (p : R) (ModuleCat.of R R) ∧ #R ≤ κ :=
    (E.inverse.obj X.unop).property
  obtain ⟨T, g, hT, hbound, hcover⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_perfectoid_arcCover p R hR.1
  let Tlarge : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffComplLarge p κ :=
    ⟨T, hT.isModuleComplete T p, hbound.trans
      ((Cardinal.power_le_power_right (add_le_add hR.2 le_rfl)).trans hκ.out)⟩
  let Y := E.functor.obj Tlarge
  let eY : F.obj Y ≅ T := (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affComplProperty p κ).ι.mapIso (E.unitIso.app Tlarge).symm
  let er : T ≃+* F.obj Y := { eY.inv.hom, ((forget CommRingCat).mapIso eY.symm).toEquiv with }
  let Yp : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.AffPerfd p κ := ⟨Y, _root_.SerrePositivity.BhattScholze.isIntegralPerfectoid_of_ringEquiv p er hT⟩
  let k : X.unop ⟶ Y :=
    F.preimage (CommRingCat.ofHom (g.comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtensionUnit p R hR.1)) ≫ eY.inv)
  refine ⟨Opposite.op Yp, k.op, ?_⟩
  have hk : (F.map k).hom = er.toRingHom.comp (g.comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtensionUnit p R hR.1)) := by
    change (F.map (F.preimage _)).hom = _
    rw [Functor.map_preimage]
    rfl
  have hY : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily p (fun _ : PUnit.{u + 1} => (F.obj Y : Type u))
      (fun _ => (F.map k).hom) := by
    intro V _ hV b
    obtain ⟨_, W, hWring, hW, m, hm, l, hl⟩ := hcover V hV b
    let : CommRing W := hWring
    refine ⟨PUnit.unit, W, hWring, hW, m, hm, l.comp er.symm.toRingHom, ?_⟩
    change l.comp (er.symm.toRingHom.comp (F.map k).hom) = m.comp b
    have he : er.symm.toRingHom.comp er.toRingHom = RingHom.id T := er.symm_comp
    rw [hk, ← RingHom.comp_assoc (g.comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtensionUnit p R hR.1)),
      he, RingHom.id_comp]
    exact hl
  change Sieve.generate (Presieve.singleton k.op) ∈ _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTopology p κ (Opposite.op X.unop)
  rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTopology, GrothendieckTopology.mem_sInf]
  intro J hJ
  have h := hJ PUnit X.unop (fun _ => Y) (fun _ => k) hY
  simpa only [Presieve.ofArrows_pUnit] using h

end SerrePositivity.BhattScholze.Perfectoidization.Derived

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Def 8.7" (partial := special) "affine・p 完備・濃度 ≤ κ 版の arc 位相。形式スキームの site は作らない ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily
attribute [cite BS19 "Def 8.7" (partial := special) "affine・p 完備・濃度 ≤ κ 版の arc 位相。形式スキームの site は作らない ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTopology
attribute [cite BS19 "Def 8.7" (partial := special) "affine・p 完備・濃度 ≤ κ 版の arc 位相。形式スキームの site は作らない ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTopologyPerfd
attribute [cite BS19 "Lemma 8.8" (partial := special) "affine 版（濃度の上界つきの整 perfectoid 一点被覆、cover-dense） ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.affPerfdInclusion_isCoverDense
attribute [cite BS19 "Lemma 8.8" (partial := special) "affine 版（濃度の上界つきの整 perfectoid 一点被覆、cover-dense） ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_perfectoid_arcCover
