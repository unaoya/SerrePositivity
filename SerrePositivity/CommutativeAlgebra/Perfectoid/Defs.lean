module

public import Mathlib.RingTheory.Perfectoid.FontaineTheta
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # 整 perfectoid 環と perfectoid 化の普遍性

## 概要

CLMST Definition 2.4.1 の四条件で整 perfectoid 環 `IsIntegralPerfectoid` を定め、perfectoid 化を perfectoid 環への写像の普遍性 `IsPerfectoidization` として表す。同じ環の二つの普遍 perfectoid 化は元の環からの写像と両立する同型を持つこと（標準写像の全射性もこれで移る）、環準同型が誘導する perfectoid 化の射（`IsPerfectoidization.map`）とその関手性、perfectoid 環自身の perfectoid 化、元の基底の上の代数写像としての比較、指定した perfectoid 化の商（excision の図式の閉じた側）を与える。

## 方針

完備性は Mathlib の `IsAdicComplete`、条件の一つは Fontaine の写像で書く。射は存在の選択によらず、普遍性だけから作る。

## 規約

長さや Koszul ホモロジーの仮定は定義に含めない。全射性を普遍性から導くことはしない。`IsIntegralPerfectoid`・`IsPerfectoidization` と `map`・`map_comp`・`map_id`・`map_map`・`lift` の名前は BS・CLMST が多く使うので変えない。旧 `CommutativeAlgebra/IntegralPerfectoid`・`PerfectoidizationUniqueness`・`PerfectoidizationFunctor`・`PerfectoidizationIdentity`・`PerfectoidizationAlgebraMap`・`PerfectoidizationQuotient`（refactor-plan §2.8.2）。

## 使われ方

`Perfectoid/Completion`・`Torsion`・`Fontaine`、BhattScholze の大半、CLMST。
-/

@[expose] public noncomputable section

universe u

section IntegralPerfectoidPart

namespace SerrePositivity

/-- 整 perfectoid 環：`p` 進完備、`p` は単元倍の `p` 乗、剰余 Frobenius は全射、
Fontaine の写像の核は単項。CLMST Definition 2.4.1。
零環も含める。Mathlib の Fontaine 写像が `p` の非可逆性を要求するため、
零環を別の場合として記す（非零の `p` 進完備環では `p` は非可逆）。 -/
def IsIntegralPerfectoid (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] : Prop :=
  Subsingleton S ∨ ∃ (hp : ¬ IsUnit (p : S))
    (hc : IsAdicComplete (Ideal.span {(p : S)}) S),
    (∃ (ϖ : S) (a : Sˣ), (p : S) = a * ϖ ^ p) ∧
    Function.Surjective (fun x : S ⧸ Ideal.span {(p : S)} ↦ x ^ p) ∧
    (letI : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
     letI := hc
     (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal)

/-- `f : S → C` が perfectoid 化であるという普遍性。
`C` は perfectoid で、任意の perfectoid 環への写像が一意に `f` を経由する。 -/
def IsPerfectoidization {S C : Type u} [CommRing S] [CommRing C]
    (p : ℕ) [Fact p.Prime] (f : S →+* C) : Prop :=
  IsIntegralPerfectoid C p ∧
    ∀ (T : Type u) [CommRing T], IsIntegralPerfectoid T p →
      ∀ g : S →+* T, ∃! l : C →+* T, l.comp f = g

end SerrePositivity

section ComposeRingEquivPart

namespace SerrePositivity

/-- perfectoid 化の普遍性は、始域の環同型に沿う前合成で保たれる。 -/
theorem IsPerfectoidization.comp_ringEquiv {S S' C : Type u}
    [CommRing S] [CommRing S'] [CommRing C]
    {p : ℕ} [Fact p.Prime] {f : S →+* C}
    (hf : IsPerfectoidization p f) (e : S' ≃+* S) :
    IsPerfectoidization p (f.comp e.toRingHom) := by
  refine ⟨hf.1, ?_⟩
  intro T _ hT g
  obtain ⟨l, hl, hu⟩ := hf.2 T hT (g.comp e.symm.toRingHom)
  refine ⟨l, ?_, ?_⟩
  · ext x
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] using
      DFunLike.congr_fun hl (e x)
  · intro l' hl'
    apply hu l'
    ext x
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] using
      DFunLike.congr_fun hl' (e.symm x)

end SerrePositivity

end ComposeRingEquivPart

end IntegralPerfectoidPart

section PerfectoidizationUniquenessPart

namespace SerrePositivity

namespace IsPerfectoidization

/-- 二つの普遍 perfectoid 化を結ぶ、元環からの写像と両立する同型。 -/
theorem exists_equiv {S C D : Type u} [CommRing S] [CommRing C] [CommRing D]
    (p : ℕ) [Fact p.Prime] {f : S →+* C} {g : S →+* D}
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g) :
    ∃ e : C ≃+* D, e.toRingHom.comp f = g := by
  obtain ⟨a, ha, hua⟩ := hf.2 D hg.1 g
  obtain ⟨b, hb, hub⟩ := hg.2 C hf.1 f
  have hba : b.comp a = RingHom.id C := by
    obtain ⟨l, hl, hul⟩ := hf.2 C hf.1 f
    exact (hul _ (by change (b.comp a).comp f = f; rw [RingHom.comp_assoc, ha, hb])).trans
      (hul _ (RingHom.id_comp f)).symm
  have hab : a.comp b = RingHom.id D := by
    obtain ⟨l, hl, hul⟩ := hg.2 D hg.1 g
    exact (hul _ (by change (a.comp b).comp g = g; rw [RingHom.comp_assoc, hb, ha])).trans
      (hul _ (RingHom.id_comp g)).symm
  exact ⟨{ a with invFun := b
                  left_inv := fun x ↦ DFunLike.congr_fun hba x
                  right_inv := fun x ↦ DFunLike.congr_fun hab x }, ha⟩

/-- 普遍対象のモデルを変えても、元環からの標準写像の全射性は変わらない。 -/
theorem surjective_iff {S C D : Type u} [CommRing S] [CommRing C] [CommRing D]
    (p : ℕ) [Fact p.Prime] {f : S →+* C} {g : S →+* D}
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g) :
    Function.Surjective f ↔ Function.Surjective g := by
  obtain ⟨e, he⟩ := hf.exists_equiv p hg
  constructor
  · intro h
    rw [← he]
    exact e.surjective.comp h
  · intro h x
    obtain ⟨s, hs⟩ := h (e x)
    refine ⟨s, e.injective ?_⟩
    exact (DFunLike.congr_fun he s).trans hs

/-- 元環で定義される核イデアルも、普遍perfectoid化のモデルに依存しない。 -/
theorem ker_eq {S C D : Type u} [CommRing S] [CommRing C] [CommRing D]
    (p : ℕ) [Fact p.Prime] {f : S →+* C} {g : S →+* D}
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g) :
    RingHom.ker f = RingHom.ker g := by
  obtain ⟨e, he⟩ := hf.exists_equiv p hg
  ext x
  change f x = 0 ↔ g x = 0
  have hx : e (f x) = g x := DFunLike.congr_fun he x
  constructor
  · intro h
    rw [← hx, h, map_zero]
  · intro h
    apply e.injective
    rw [hx, h, map_zero]

end IsPerfectoidization
end SerrePositivity

end PerfectoidizationUniquenessPart

section PerfectoidizationFunctorPart

namespace SerrePositivity
namespace IsPerfectoidization

variable {S C T D U E : Type u}
    [CommRing S] [CommRing C] [CommRing T] [CommRing D] [CommRing U] [CommRing E]
    {p : ℕ} [Fact p.Prime] {f : S →+* C} {g : T →+* D} {h : U →+* E}

/-- perfectoid 化の普遍性で保証される因子分解を選ぶ。 -/
def lift (hf : IsPerfectoidization p f) (hD : IsIntegralPerfectoid D p) (k : S →+* D) :
    C →+* D := (hf.2 D hD k).choose

/-- 選んだ因子分解は元の写像と両立する。 -/
theorem lift_comp (hf : IsPerfectoidization p f) (hD : IsIntegralPerfectoid D p) (k : S →+* D) :
    (lift hf hD k).comp f = k := (hf.2 D hD k).choose_spec.1

/-- 普遍写像との合成が同じ射は、選んだ因子分解に一致する。 -/
theorem lift_unique (hf : IsPerfectoidization p f) (hD : IsIntegralPerfectoid D p)
    (k : S →+* D) (l : C →+* D) (hl : l.comp f = k) : l = lift hf hD k :=
  (hf.2 D hD k).choose_spec.2 l hl

/-- Changing the presentation of the source preserves its universal perfectoidization. -/
theorem precomp_ringEquiv (hf : IsPerfectoidization p f) (e : T ≃+* S) :
    IsPerfectoidization p (f.comp e.toRingHom) := by
  refine ⟨hf.1, ?_⟩
  intro U _ hU k
  obtain ⟨l, hl, huniq⟩ := hf.2 U hU (k.comp e.symm.toRingHom)
  refine ⟨l, ?_, ?_⟩
  · apply RingHom.ext
    intro x
    change l (f (e x)) = k x
    have hx := RingHom.congr_fun hl (e x)
    change l (f (e x)) = k (e.symm (e x)) at hx
    simpa only [e.symm_apply_apply] using hx
  · intro m hm
    apply huniq
    apply RingHom.ext
    intro x
    change m (f x) = k (e.symm x)
    have hx := RingHom.congr_fun hm (e.symm x)
    change m (f (e (e.symm x))) = k (e.symm x) at hx
    simpa only [e.apply_symm_apply] using hx

/-- 環準同型を、固定した二つの perfectoid 化の間の射へ移す。 -/
def map (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g) (k : S →+* T) :
    C →+* D := lift hf hg.1 (g.comp k)

/-- 誘導射は二つの普遍写像と元の環準同型の図式を可換にする。 -/
theorem map_comp (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g) (k : S →+* T) :
    (map hf hg k).comp f = g.comp k := lift_comp hf hg.1 _

/-- perfectoid 化の恒等射への誘導射は恒等射。 -/
theorem map_id (hf : IsPerfectoidization p f) : map hf hf (RingHom.id S) = RingHom.id C := by
  apply Eq.symm
  apply lift_unique hf hf.1 (f.comp (RingHom.id S))
  ext x
  rfl

/-- perfectoid 化への誘導射は合成と両立する。 -/
theorem map_map (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (hh : IsPerfectoidization p h) (k : S →+* T) (l : T →+* U) :
    (map hg hh l).comp (map hf hg k) = map hf hh (l.comp k) := by
  apply lift_unique hf hh.1 (h.comp (l.comp k))
  rw [RingHom.comp_assoc, map_comp, ← RingHom.comp_assoc, map_comp, RingHom.comp_assoc]

end IsPerfectoidization

namespace IsPerfectoidization
/-- 普遍対象の選択を変えても、任意の元環から合成した写像の核は一致する。 -/
theorem ker_comp_eq {R S C D : Type u}
    [CommRing R] [CommRing S] [CommRing C] [CommRing D]
    (p : ℕ) [Fact p.Prime] {f : S →+* C} {g : S →+* D}
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g) (q : R →+* S) :
    RingHom.ker (f.comp q) = RingHom.ker (g.comp q) := by
  ext x
  change q x ∈ RingHom.ker f ↔ q x ∈ RingHom.ker g
  rw [hf.ker_eq p hg]
end IsPerfectoidization
end SerrePositivity

end PerfectoidizationFunctorPart

section PerfectoidizationIdentityPart

namespace SerrePositivity

/-- The identity on an already perfectoid ring is its universal perfectoidization. -/
theorem IsIntegralPerfectoid.isPerfectoidization_id
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    IsPerfectoidization p (RingHom.id R) := by
  refine ⟨hR, ?_⟩
  intro T _ _ k
  refine ⟨k, RingHom.comp_id k, ?_⟩
  intro l hl
  simpa only [RingHom.comp_id] using hl

end SerrePositivity

end PerfectoidizationIdentityPart

section PerfectoidizationAlgebraMapPart

namespace SerrePositivity.IsPerfectoidization
variable {R A B C D : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] {f : A →ₐ[R] C} {g : B →ₐ[R] D}

/-- The universal comparison retains the pre-existing algebra structures over R. -/
def mapAlgHom (hf : IsPerfectoidization p f.toRingHom)
    (hg : IsPerfectoidization p g.toRingHom) (q : A →ₐ[R] B) : C →ₐ[R] D where
  __ := IsPerfectoidization.map hf hg q.toRingHom
  commutes' r := by
    have h := RingHom.congr_fun (hf.map_comp hg q.toRingHom) (algebraMap R A r)
    change IsPerfectoidization.map hf hg q.toRingHom (f (algebraMap R A r)) =
      g (q (algebraMap R A r)) at h
    rw [f.commutes, q.commutes, g.commutes] at h
    exact h

/-- Forgetting R-linearity recovers precisely the original functorial ring map. -/
@[simp] theorem mapAlgHom_toRingHom (hf : IsPerfectoidization p f.toRingHom)
    (hg : IsPerfectoidization p g.toRingHom) (q : A →ₐ[R] B) :
    (mapAlgHom hf hg q).toRingHom = IsPerfectoidization.map hf hg q.toRingHom := rfl

/-- The scalar-preserving comparison commutes with the original universal maps. -/
theorem mapAlgHom_comp (hf : IsPerfectoidization p f.toRingHom)
    (hg : IsPerfectoidization p g.toRingHom) (q : A →ₐ[R] B) :
    (mapAlgHom hf hg q).comp f = g.comp q := by
  ext a
  exact RingHom.congr_fun (hf.map_comp hg q.toRingHom) a

/-- Functorial composition retains the same original scalar action. -/
theorem mapAlgHom_mapAlgHom {U E : Type u} [CommRing U] [CommRing E]
    [Algebra R U] [Algebra R E] {h : U →ₐ[R] E}
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (hh : IsPerfectoidization p h.toRingHom)
    (q : A →ₐ[R] B) (r : B →ₐ[R] U) :
    (mapAlgHom hg hh r).comp (mapAlgHom hf hg q) = mapAlgHom hf hh (r.comp q) := by
  ext x
  exact RingHom.congr_fun (hf.map_map hg hh q.toRingHom r.toRingHom) x

end SerrePositivity.IsPerfectoidization

end PerfectoidizationAlgebraMapPart

section PerfectoidizationQuotientPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.IsPerfectoidization
variable {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    {p : ℕ} [Fact p.Prime] {f : A →+* C}

/-- Perfectoidizing the quotient of C by the image of J also perfectoidizes A/J,
through the actual induced quotient map of the original universal unit. -/
theorem quotient_map (hf : IsPerfectoidization p f) (J : Ideal A)
    (h : C ⧸ J.map f →+* D) (hh : IsPerfectoidization p h) :
    IsPerfectoidization p
      (h.comp (Ideal.quotientMap (J.map f) f Ideal.le_comap_map)) := by
  refine ⟨hh.1, ?_⟩
  intro T _ hT k
  let a : A →+* A ⧸ J := Ideal.Quotient.mk J
  let c : C →+* C ⧸ J.map f := Ideal.Quotient.mk (J.map f)
  obtain ⟨l, hl, hu⟩ := hf.2 T hT (k.comp a)
  have hker : J.map f ≤ RingHom.ker l := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change l (f x) = 0
    have he := RingHom.congr_fun hl x
    change l (f x) = k (a x) at he
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero] at he
    exact he
  let q : C ⧸ J.map f →+* T := Ideal.Quotient.lift _ l (fun x hx => hker hx)
  obtain ⟨L, hL, huniq⟩ := hh.2 T hT q
  have hLk : L.comp (h.comp (Ideal.quotientMap (J.map f) f Ideal.le_comap_map)) = k := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    change L (h (c (f x))) = k (a x)
    exact (RingHom.congr_fun hL (c (f x))).trans (RingHom.congr_fun hl x)
  refine ⟨L, hLk, ?_⟩
  intro m hm
  apply huniq
  apply Ideal.Quotient.ringHom_ext
  change (m.comp h).comp c = l
  apply hu
  ext x
  exact RingHom.congr_fun hm (a x)

end SerrePositivity.IsPerfectoidization

end PerfectoidizationQuotientPart
