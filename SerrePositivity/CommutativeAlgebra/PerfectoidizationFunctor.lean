module

public import SerrePositivity.CommutativeAlgebra.PerfectoidizationUniqueness

/-! # 存在の選択と独立したperfectoid化の関手性 -/

@[expose] public noncomputable section
universe u
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
