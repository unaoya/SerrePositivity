module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedBaseChange
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.Surjectivity

/-!
# perfectoid 化と完備テンソル積の可換性（BS 著者版 Proposition 8.13 の環版）

## 概要
指定済みの環の perfectoid 化をもつ一般のテンソル図式で、完備テンソル積の perfectoid 化は perfectoid 化の完備テンソル積。perfectoid な底変換の場合。

## 方針
環の普遍性、H⁰ 主元完備化の比較、perfectoid 完備テンソル定理の合成。

## 規約
ここでは環の比較を述べる。E∞ 代数の版は Δ の対称モノイダル性を用いる別の構成である。

## 使われ方
CLMST、Lemma 10.3。
-/

universe u

/-! ## Ring-perfectoidization of a general tensor diagram

This is the ring-valued pushout statement underlying BS 著者版 Proposition 8.13.
The three specified perfectoidizations form a compatible diagram. Its
completed tensor is supplied by the existing perfectoid tensor theorem, rather
than by rebuilding prismatic cohomology or its symmetric monoidal structure.
-/

@[expose] public noncomputable section PerfectoidizationTensorCompatibility

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R S T P C D : Type u}
    [CommRing R] [CommRing S] [CommRing T] [CommRing P] [CommRing C] [CommRing D]
    [Algebra R S] [Algebra R T] [Algebra P C] [Algebra P D]
    (r : R →+* P) (s : S →+* C) (t : T →+* D)
    (hs : ∀ x, s (algebraMap R S x) = algebraMap P C (r x))
    (ht : ∀ x, t (algebraMap R T x) = algebraMap P D (r x))

/-- The ordinary tensor map of the original diagram into the tensor of its
specified perfectoidizations, balanced over the specified new base. -/
def perfectoidizationTensorDiagramMap : S ⊗[R] T →+* C ⊗[P] D :=
  _root_.SerrePositivity.coefficientTensorLift
    ((Algebra.TensorProduct.includeLeft : C →ₐ[P] C ⊗[P] D).toRingHom.comp s)
    ((Algebra.TensorProduct.includeRight : D →ₐ[P] C ⊗[P] D).toRingHom.comp t)
    (fun x => by
      change (Algebra.TensorProduct.includeLeft : C →ₐ[P] C ⊗[P] D)
          (s (algebraMap R S x)) =
        (Algebra.TensorProduct.includeRight : D →ₐ[P] C ⊗[P] D)
          (t (algebraMap R T x))
      rw [hs, ht]
      exact ((Algebra.TensorProduct.includeLeft : C →ₐ[P] C ⊗[P] D).commutes (r x)).trans
        ((Algebra.TensorProduct.includeRight : D →ₐ[P] C ⊗[P] D).commutes (r x)).symm)

/-- The diagram map retains both specified factor maps on every pure tensor. -/
lemma perfectoidizationTensorDiagramMap_tmul (x : S) (y : T) :
    perfectoidizationTensorDiagramMap r s t hs ht (x ⊗ₜ[R] y) = s x ⊗ₜ[P] t y := by
  change (s x ⊗ₜ[P] (1 : D)) * ((1 : C) ⊗ₜ[P] t y) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

variable (p : ℕ) [Fact p.Prime]

/-- The tensor of three compatible ring-perfectoidizations is universal among
perfectoid targets. No flatness, completeness, or surjectivity of the original
diagram is needed for this ring-valued universal property. -/
lemma perfectoidizationTensorDiagramMap_isPerfectoidization
    (hr : IsPerfectoidization p r) (hsp : IsPerfectoidization p s)
    (htp : IsPerfectoidization p t) (E : Type u) [CommRing E]
    (f : C ⊗[P] D →+* E) (hf : IsPerfectoidization p f) :
    IsPerfectoidization p (f.comp (perfectoidizationTensorDiagramMap r s t hs ht)) := by
  let iC := (Algebra.TensorProduct.includeLeft : C →ₐ[P] C ⊗[P] D).toRingHom
  let iD := (Algebra.TensorProduct.includeRight : D →ₐ[P] C ⊗[P] D).toRingHom
  let jS := (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom
  let jT := (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom
  refine ⟨hf.1, ?_⟩
  intro U _ hU g
  obtain ⟨lC, hlC, huniqC⟩ := hsp.2 U hU (g.comp jS)
  obtain ⟨lD, hlD, huniqD⟩ := htp.2 U hU (g.comp jT)
  have hbase : lC.comp (algebraMap P C) = lD.comp (algebraMap P D) := by
    apply (hr.2 U hU ((lC.comp (algebraMap P C)).comp r)).unique rfl
    ext x
    change lD (algebraMap P D (r x)) = lC (algebraMap P C (r x))
    rw [← hs, ← ht]
    calc
      lD (t (algebraMap R T x)) = g (jT (algebraMap R T x)) :=
        RingHom.congr_fun hlD _
      _ = g (jS (algebraMap R S x)) := congrArg g
        (((Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).commutes x).trans
          ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).commutes x).symm)
      _ = lC (s (algebraMap R S x)) := (RingHom.congr_fun hlC _).symm
  let k : C ⊗[P] D →+* U := _root_.SerrePositivity.coefficientTensorLift lC lD (RingHom.congr_fun hbase)
  obtain ⟨l, hl, huniq⟩ := hf.2 U hU k
  have hlg : l.comp (f.comp (perfectoidizationTensorDiagramMap r s t hs ht)) = g := by
    apply RingHom.ext
    intro z
    refine TensorProduct.inductionOn z (fun x y => ?_) (fun x y hx hy => ?_)
    · change l (f (perfectoidizationTensorDiagramMap r s t hs ht (x ⊗ₜ[R] y))) =
        g (x ⊗ₜ[R] y)
      rw [perfectoidizationTensorDiagramMap_tmul]
      have hh := RingHom.congr_fun hl (s x ⊗ₜ[P] t y)
      change l (f (s x ⊗ₜ[P] t y)) = lC (s x) * lD (t y) at hh
      have hc : lC (s x) = g (jS x) := RingHom.congr_fun hlC x
      have hd : lD (t y) = g (jT y) := RingHom.congr_fun hlD y
      rw [hh, hc, hd, ← map_mul]
      congr 1
      change (x ⊗ₜ[R] (1 : T)) * ((1 : S) ⊗ₜ[R] y) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · simp only [map_add, hx, hy]
  refine ⟨l, hlg, ?_⟩
  intro m hm
  have hmC : (m.comp (f.comp iC)).comp s = g.comp jS := by
    ext x
    have hh := RingHom.congr_fun hm (x ⊗ₜ[R] (1 : T))
    change m (f (perfectoidizationTensorDiagramMap r s t hs ht (x ⊗ₜ[R] 1))) = _ at hh
    rw [perfectoidizationTensorDiagramMap_tmul, map_one] at hh
    exact hh
  have hmD : (m.comp (f.comp iD)).comp t = g.comp jT := by
    ext y
    have hh := RingHom.congr_fun hm ((1 : S) ⊗ₜ[R] y)
    change m (f (perfectoidizationTensorDiagramMap r s t hs ht (1 ⊗ₜ[R] y))) = _ at hh
    rw [perfectoidizationTensorDiagramMap_tmul, map_one] at hh
    exact hh
  have heC : m.comp (f.comp iC) = lC := huniqC _ hmC
  have heD : m.comp (f.comp iD) = lD := huniqD _ hmD
  apply huniq
  apply RingHom.ext
  intro z
  refine TensorProduct.inductionOn z (fun x y => ?_) (fun x y hx hy => ?_)
  · have hxy : x ⊗ₜ[P] y = iC x * iD y := by
      change x ⊗ₜ[P] y = (x ⊗ₜ[P] (1 : D)) * ((1 : C) ⊗ₜ[P] y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    change m (f (x ⊗ₜ[P] y)) = lC x * lD y
    have hc : m (f (iC x)) = lC x := RingHom.congr_fun heC x
    have hd : m (f (iD y)) = lD y := RingHom.congr_fun heD y
    rw [hxy, map_mul, map_mul, hc, hd]
  · simp only [map_add, hx, hy]

end SerrePositivity.BhattScholze

end PerfectoidizationTensorCompatibility

/-! ## BS 著者版 Proposition 8.13 in the ring-valued reflection domain

For any compatible diagram of three specified ring-perfectoidizations, the
original completed tensor of the perfectoid rings is discrete and perfectoid.
Its actual H⁰ is the ring-perfectoidization of the actual original completed
tensor H⁰. The comparison preserves the original units and both factor maps.

The author-version proposition, pp. 69–70, concerns arbitrary derived p-complete
simplicial rings over a perfectoid ring and their derived E∞ perfectoidizations.
Here the ring-perfectoidizations are specified, rather than presumed to exist
for all rings. No identification of an arbitrary derived tensor with its H⁰ is
made. The proof uses the existing completion comparison and the ring universal property
instead of the original argument via symmetric monoidal prismatic cohomology.
-/

@[expose] public noncomputable section PerfectoidizationCompletedTensorCompatibility

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] {R S T P C D : Type u}
    [CommRing R] [CommRing S] [CommRing T] [CommRing P] [CommRing C] [CommRing D]
    [Algebra R S] [Algebra R T] [Algebra P C] [Algebra P D]
    (r : R →+* P) (s : S →+* C) (t : T →+* D)
    (hs : ∀ x, s (algebraMap R S x) = algebraMap P C (r x))
    (ht : ∀ x, t (algebraMap R T x) = algebraMap P D (r x))
local notation "X" => boundedAboveCompletedTensorAlgebra R (p : R) S T
local notation "Y" => boundedAboveCompletedTensorAlgebra P (p : P) C D
set_option quotPrecheck false in
local notation "HX" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (X).X.obj
set_option quotPrecheck false in
local notation "HY" => (DerivedCategory.homologyFunctor (ModuleCat P) 0).obj (Y).X.obj

/-- The original tensor unit followed by the original completed target unit. -/
def prop813TensorMap :
    letI := derivedH0CommRing Y
    S ⊗[R] T →+* HY := by
  letI := derivedH0CommRing Y
  exact (completedTensorPerfectoidizationMap P p C D).comp
    (perfectoidizationTensorDiagramMap r s t hs ht)

/-- The specified completed perfectoid tensor is the universal perfectoid target
of the original ordinary tensor diagram. -/
lemma prop813TensorMap_isPerfectoidization
    (hr : IsPerfectoidization p r) (hsp : IsPerfectoidization p s)
    (htp : IsPerfectoidization p t) :
    letI := derivedH0CommRing Y
    IsPerfectoidization p (prop813TensorMap p r s t hs ht) := by
  let := derivedH0CommRing Y
  exact perfectoidizationTensorDiagramMap_isPerfectoidization r s t hs ht p hr hsp htp _
    (completedTensorPerfectoidizationMap P p C D)
    (completedTensorPerfectoidizationMap_isPerfectoidization P p C D hr.1 hsp.1 htp.1)

variable (hr : IsPerfectoidization p r) (hsp : IsPerfectoidization p s)
    (htp : IsPerfectoidization p t)

/-- Extend the specified tensor diagram over its original actual H⁰ completion unit. -/
def prop813CompletedTensorMap :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    HX →+* HY := by
  letI := derivedH0CommRing X
  letI := derivedH0CommRing Y
  exact completedTensorPerfectoidLift R p S T _
    (prop813TensorMap_isPerfectoidization p r s t hs ht hr hsp htp).1
    (prop813TensorMap p r s t hs ht)

/-- The map commutes with the original completion-unit square. -/
lemma prop813CompletedTensorMap_comp_unit :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    (prop813CompletedTensorMap p r s t hs ht hr hsp htp).comp
      (completedTensorPerfectoidizationMap R p S T) = prop813TensorMap p r s t hs ht := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  exact completedTensorPerfectoidLift_comp R p S T _ _ _

/-- Both original factor maps are retained on each pure tensor class. -/
lemma prop813CompletedTensorMap_unit_tmul (x : S) (y : T) :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    prop813CompletedTensorMap p r s t hs ht hr hsp htp
      (completedTensorPerfectoidizationMap R p S T (x ⊗ₜ[R] y)) =
        completedTensorPerfectoidizationMap P p C D (s x ⊗ₜ[P] t y) := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  have h := RingHom.congr_fun
    (prop813CompletedTensorMap_comp_unit p r s t hs ht hr hsp htp) (x ⊗ₜ[R] y)
  change _ = completedTensorPerfectoidizationMap P p C D
    (perfectoidizationTensorDiagramMap r s t hs ht (x ⊗ₜ[R] y)) at h
  simpa only [RingHom.comp_apply, perfectoidizationTensorDiagramMap_tmul] using h

/-- 指定した普遍 perfectoid 化の完備テンソルの H⁰ は、元の完備テンソルの H⁰ の
普遍 perfectoid 化を与える（BS 著者版 Proposition 8.13 の環としての完備テンソル版）。 -/
lemma prop813CompletedTensorMap_isPerfectoidization :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    IsPerfectoidization p (prop813CompletedTensorMap p r s t hs ht hr hsp htp) := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  exact completedTensorPerfectoidLift_isPerfectoidization R p S T _ _
    (prop813TensorMap_isPerfectoidization p r s t hs ht hr hsp htp)

omit [Algebra R S] [Algebra R T] in
include hr hsp htp in
/-- The perfectoidized tensor in this statement is the original discrete
completed derived tensor, not a replacement chosen only at the level of H⁰. -/
lemma prop813_perfectoidTensor_pure : (Y).X.obj.IsGE 0 ∧ (Y).X.obj.IsLE 0 :=
  integralPerfectoid_completedTensor_pure p P C D hr.1 hsp.1 htp.1

/-- The standard comparison with any specified ring-perfectoidization of the
original completed tensor. Its orientation is the one in BS 著者版 Proposition 8.13. -/
def prop813ComparisonEquiv (E : Type u) [CommRing E] :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    ∀ (g : HX →+* E), IsPerfectoidization p g → HY ≃+* E := by
  letI := derivedH0CommRing X
  letI := derivedH0CommRing Y
  intro g hg
  exact ((prop813CompletedTensorMap_isPerfectoidization p r s t hs ht hr hsp htp).exists_equiv
    p hg).choose

/-- The comparison preserves the entire original completed-tensor map. -/
lemma prop813ComparisonEquiv_comp (E : Type u) [CommRing E] :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    ∀ (g : HX →+* E) (hg : IsPerfectoidization p g),
      (prop813ComparisonEquiv p r s t hs ht hr hsp htp E g hg).toRingHom.comp
        (prop813CompletedTensorMap p r s t hs ht hr hsp htp) = g := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  intro g hg
  exact ((prop813CompletedTensorMap_isPerfectoidization p r s t hs ht hr hsp htp).exists_equiv
    p hg).choose_spec

/-- A comparison retaining the original unit is unique, so the equivalence does
not depend on an additional choice of comparison map. -/
lemma prop813ComparisonEquiv_unique (E : Type u) [CommRing E] :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    ∀ (g : HX →+* E) (hg : IsPerfectoidization p g) (f : HY →+* E),
      f.comp (prop813CompletedTensorMap p r s t hs ht hr hsp htp) = g →
        f = (prop813ComparisonEquiv p r s t hs ht hr hsp htp E g hg).toRingHom := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  intro g hg f hf
  exact ((prop813CompletedTensorMap_isPerfectoidization p r s t hs ht hr hsp htp).2 E hg.1 g).unique
    hf (prop813ComparisonEquiv_comp p r s t hs ht hr hsp htp E g hg)

/-- The inverse comparison also retains the entire original completed-tensor map. -/
lemma prop813ComparisonEquiv_symm_comp (E : Type u) [CommRing E] :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    ∀ (g : HX →+* E) (hg : IsPerfectoidization p g),
      (prop813ComparisonEquiv p r s t hs ht hr hsp htp E g hg).symm.toRingHom.comp g =
        prop813CompletedTensorMap p r s t hs ht hr hsp htp := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  intro g hg
  let e := prop813ComparisonEquiv p r s t hs ht hr hsp htp E g hg
  apply RingHom.ext
  intro x
  apply e.injective
  change e (e.symm (g x)) = e (prop813CompletedTensorMap p r s t hs ht hr hsp htp x)
  rw [e.apply_symm_apply]
  exact (RingHom.congr_fun
    (prop813ComparisonEquiv_comp p r s t hs ht hr hsp htp E g hg) x).symm

end SerrePositivity.BhattScholze

end PerfectoidizationCompletedTensorCompatibility

/-! ## The ring form of BS 著者版 Proposition 8.13 for perfectoid base change

The base and new base are perfectoid. The original algebra is arbitrary once its
ring-perfectoidization is specified. The map out of the original completed
tensor H⁰ and the comparison preserve the new-base action and the original unit.

In particular this applies to p-completely flat perfectoid base change. Flatness
is unnecessary for this H⁰ ring universal property. Discreteness of the original
completed tensor, or comparison with a classical completed tensor, is a separate
input; no unbounded p-torsion case is silently replaced by classical completion.
-/

@[expose] public noncomputable section Prop813PerfectoidBaseChange

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (S A C : Type u)
    [CommRing S] [CommRing A] [CommRing C] [Algebra R S] [Algebra R A] [Algebra R C]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
local notation "X" => boundedAboveCompletedTensorAlgebra R (p : R) S A
local notation "Y" => boundedAboveCompletedTensorAlgebra R (p : R) S C
set_option quotPrecheck false in
local notation "HX" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (X).X.obj
set_option quotPrecheck false in
local notation "HY" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (Y).X.obj

/-- The specified perfectoidization map after actual completed base change. -/
def prop813BaseChangeMap :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    HX →+* HY := by
  letI := derivedH0CommRing X
  letI := derivedH0CommRing Y
  exact completedTensorPerfectoidLift R p S A _
    (perfectoidizationCompletedBaseChangeMap_isPerfectoidization R p S A C hR hS f hf).1
    (perfectoidizationCompletedBaseChangeMap R p S A C f)

/-- The original ordinary-tensor diagram and actual completion units commute. -/
lemma prop813BaseChangeMap_comp_unit :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    (prop813BaseChangeMap R p S A C hR hS f hf).comp
      (completedTensorPerfectoidizationMap R p S A) =
        perfectoidizationCompletedBaseChangeMap R p S A C f := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  exact completedTensorPerfectoidLift_comp R p S A _ _ _

/-- The base change retains the specified map of the original algebra on every
pure tensor, together with the original new-base coefficient. -/
lemma prop813BaseChangeMap_unit_tmul (b : S) (a : A) :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    prop813BaseChangeMap R p S A C hR hS f hf
      (completedTensorPerfectoidizationMap R p S A (b ⊗ₜ[R] a)) =
        completedTensorPerfectoidizationMap R p S C (b ⊗ₜ[R] f a) := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  have h := RingHom.congr_fun
    (prop813BaseChangeMap_comp_unit R p S A C hR hS f hf) (b ⊗ₜ[R] a)
  change prop813BaseChangeMap R p S A C hR hS f hf
    (completedTensorPerfectoidizationMap R p S A (b ⊗ₜ[R] a)) =
      completedTensorPerfectoidizationMap R p S C (b ⊗ₜ[R] f a) at h
  exact h

/-- The actual completed base change is a ring-perfectoidization of the original
actual completed tensor H⁰. No finite presentation or torsion bound is added. -/
lemma prop813BaseChangeMap_isPerfectoidization :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    IsPerfectoidization p (prop813BaseChangeMap R p S A C hR hS f hf) := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  exact completedTensorPerfectoidLift_isPerfectoidization R p S A _ _
    (perfectoidizationCompletedBaseChangeMap_isPerfectoidization R p S A C hR hS f hf)

/-- The map retains the original new-base factor, including its actual H⁰ algebra action. -/
lemma prop813BaseChangeMap_left (b : S) :
    letI := derivedH0CommRing X
    letI := derivedH0Algebra X
    letI := derivedH0CommRing Y
    letI := derivedH0Algebra Y
    prop813BaseChangeMap R p S A C hR hS f hf
      (completedTensorH0LeftAlgHom R (p : R) S A b) =
        completedTensorH0LeftAlgHom R (p : R) S C b := by
  let := derivedH0CommRing X
  let := derivedH0Algebra X
  let := derivedH0CommRing Y
  let := derivedH0Algebra Y
  rw [← completedTensorPerfectoidizationMap_left R p S A b]
  have h := RingHom.congr_fun (prop813BaseChangeMap_comp_unit R p S A C hR hS f hf)
    (b ⊗ₜ[R] (1 : A))
  change prop813BaseChangeMap R p S A C hR hS f hf
    (completedTensorPerfectoidizationMap R p S A (b ⊗ₜ[R] 1)) =
      perfectoidizationCompletedBaseChangeMap R p S A C f (b ⊗ₜ[R] 1) at h
  exact h.trans (perfectoidizationCompletedBaseChangeMap_left R p S A C f b)

/-- BS 著者版 Proposition 8.13, ring base-change form: comparison with any specified
perfectoidization of the original completed tensor preserves the new base and
the entire completed base-change map. -/
lemma prop813BaseChange_exists_algEquiv (E : Type u) [CommRing E] [Algebra S E] :
    letI := derivedH0CommRing X
    letI := derivedH0Algebra X
    letI := completedTensorH0LeftAlgebra R (p : R) S A
    letI := derivedH0CommRing Y
    letI := derivedH0Algebra Y
    letI := completedTensorH0LeftAlgebra R (p : R) S C
    ∀ (g : HX →ₐ[S] E), IsPerfectoidization p g.toRingHom →
      ∃ e : HY ≃ₐ[S] E,
        e.toRingHom.comp (prop813BaseChangeMap R p S A C hR hS f hf) = g.toRingHom := by
  let := derivedH0CommRing X
  let := derivedH0Algebra X
  let := completedTensorH0LeftAlgebra R (p : R) S A
  let := derivedH0CommRing Y
  let := derivedH0Algebra Y
  let := completedTensorH0LeftAlgebra R (p : R) S C
  intro g hg
  obtain ⟨e, he⟩ :=
    (prop813BaseChangeMap_isPerfectoidization R p S A C hR hS f hf).exists_equiv p hg
  have hc (b : S) : e (algebraMap S HY b) = algebraMap S E b := by
    have hb : prop813BaseChangeMap R p S A C hR hS f hf (algebraMap S HX b) =
        algebraMap S HY b := prop813BaseChangeMap_left R p S A C hR hS f hf b
    rw [← hb]
    exact (RingHom.congr_fun he (algebraMap S HX b)).trans (g.commutes b)
  exact ⟨AlgEquiv.ofRingEquiv (f := e) hc, he⟩

/-- An ordinary-tensor perfectoidization suffices: extend its original unit and
obtain the same new-base algebra comparison on the actual completed source. -/
lemma prop813BaseChange_exists_algEquiv_of_tensor
    (E : Type u) [CommRing E] [Algebra S E]
    (g : S ⊗[R] A →ₐ[S] E) (hg : IsPerfectoidization p g.toRingHom) :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    letI := derivedH0Algebra Y
    letI := completedTensorH0LeftAlgebra R (p : R) S C
    ∃ e : HY ≃ₐ[S] E,
      e.toRingHom.comp (prop813BaseChangeMap R p S A C hR hS f hf) =
        completedTensorPerfectoidLift R p S A E hg.1 g.toRingHom := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  let := derivedH0Algebra Y
  let := completedTensorH0LeftAlgebra R (p : R) S C
  obtain ⟨e, he⟩ := perfectoidizationCompletedBaseChangeMap_exists_algEquiv
    R p S A C hR hS f hf E g hg
  refine ⟨e, ?_⟩
  apply completedTensorPerfectoid_hom_ext R p S A E hg.1
  rw [RingHom.comp_assoc, prop813BaseChangeMap_comp_unit, he, completedTensorPerfectoidLift_comp]

include hR hS f hf in
/-- The comparison also applies to the actual new-base G2 H⁰ module, with its
original new-base action rather than only the restricted old-base action. -/
lemma prop813BaseChange_exists_linearEquiv (E : Type u) [CommRing E] [Algebra S E] :
    letI := derivedH0CommRing X
    letI := derivedH0Algebra X
    letI := completedTensorH0LeftAlgebra R (p : R) S A
    ∀ (g : HX →ₐ[S] E), IsPerfectoidization p g.toRingHom →
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
        ((boundedAboveDerivedCompletionFunctor S (p : S)).obj
          ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))).obj ≃ₗ[S] E) := by
  let := derivedH0CommRing X
  let := derivedH0Algebra X
  let := completedTensorH0LeftAlgebra R (p : R) S A
  let := derivedH0CommRing Y
  let := derivedH0Algebra Y
  let := completedTensorH0LeftAlgebra R (p : R) S C
  intro g hg
  obtain ⟨e, _he⟩ := prop813BaseChange_exists_algEquiv R p S A C hR hS f hf E g hg
  have eH := completedBaseChangeTensorH0LinearEquiv R S C (p : R)
  rw [map_natCast] at eH
  exact ⟨eH.trans e.toLinearEquiv⟩

/-- perfectoid 環の全射商の普遍 perfectoid 化を取り、その完備底変換も普遍 perfectoid 化になる
（BS 著者版 Proposition 8.13 の環版で片方が perfectoid 環の全射商の場合）。
方針：全射商の普遍 perfectoid 化の存在から指定の写像を取り、環の完備底変換の比較を適用する。 -/
theorem exists_prop813BaseChange_of_perfectoid_quotient
    (hq : Function.Surjective (algebraMap R A)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (f : A →ₐ[R] C),
      ∃ hf : IsPerfectoidization p f.toRingHom,
        letI := derivedH0CommRing X
        letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S C)
        IsPerfectoidization p (prop813BaseChangeMap R p S A C hR hS f hf) := by
  obtain ⟨C, hC, f, hf⟩ :=
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_perfectoid_surjective_quotient hR (algebraMap R A) hq
  let := hC
  let hRC : Algebra R C := (f.comp (algebraMap R A)).toAlgebra
  let fA : A →ₐ[R] C := { f with commutes' := fun _ => rfl }
  have hfA : IsPerfectoidization p fA.toRingHom := hf
  exact ⟨C, hC, hRC, fA, hfA,
    prop813BaseChangeMap_isPerfectoidization R p S A C hR hS fA hfA⟩

/-- For a derived p-complete quotient, B4 also makes the original specified
perfectoidization surjective. General p-torsion quotients are included. -/
theorem exists_prop813BaseChange_of_semiperfectoid_quotient
    (hq : Function.Surjective (algebraMap R A))
    (hA : IsModuleComplete A (p : A) (ModuleCat.of A A)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (f : A →ₐ[R] C),
      ∃ hf : IsPerfectoidization p f.toRingHom,
        Function.Surjective f ∧
          (letI := derivedH0CommRing X
           letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S C)
           IsPerfectoidization p (prop813BaseChangeMap R p S A C hR hS f hf)) := by
  obtain ⟨C, hC, hRC, f, hf, hbase⟩ :=
    exists_prop813BaseChange_of_perfectoid_quotient R p S A hR hS hq
  let := hC
  let := hRC
  exact ⟨C, hC, hRC, f, hf,
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_semiperfectoid_quotient hR
      (algebraMap R A) hq hA f.toRingHom hf, hbase⟩

end SerrePositivity.BhattScholze

end Prop813PerfectoidBaseChange

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Prop 8.13" (partial := special) "本体は環版だけ（指定済みの環の perfectoid 化を仮定した完備テンソルの可換性、sorry 0、E3 に到達しない）。Cor 8.14 に要る導来版（Δ の対称モノイダル性経由）は drafts ／ DOC1 照合：ok 2 件"] _root_.SerrePositivity.BhattScholze.exists_prop813BaseChange_of_perfectoid_quotient
attribute [cite BS19 "Prop 8.13" (partial := special) "本体は環版だけ（指定済みの環の perfectoid 化を仮定した完備テンソルの可換性、sorry 0、E3 に到達しない）。Cor 8.14 に要る導来版（Δ の対称モノイダル性経由）は drafts ／ DOC1 照合：ok 2 件"] _root_.SerrePositivity.BhattScholze.prop813CompletedTensorMap_isPerfectoidization
