module

public import SerrePositivity.BhattScholze.Prism.PCompletedDeltaDivisionComparison
public import SerrePositivity.BhattScholze.Delta.PerfectDeltaFrobenius

/-! # 異なる二つの除算元族の段階的添加と一括添加

著者公開版Prop 7.2のδ除算普遍性を、具体的な完全p進完備δ候補について使う。
aを添加した候補にbの像を添加する二段構成と、a,bを一括添加する候補を比較する。
導来(p,d)完備化の超限反復やperfectoid化とは同定しない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
variable {σ : Type v} {τ : Type w}

/-- aを添加した候補でbの基底像をさらに添加する、具体的な二段候補。 -/
abbrev SequentialPCompletedDeltaDivision
    (D : DeltaStructure p R) (d : R) (a : σ → R) (b : τ → R) :=
  PCompletedDeltaDivision (pCompletedDeltaDivisionStructure D d a)
    (pCompletedDeltaDivisionMap D d a d) (fun t ↦ pCompletedDeltaDivisionMap D d a (b t))

/-- 二段候補のδ構造は二段目の既存のδ構造。 -/
abbrev sequentialPCompletedDeltaDivisionStructure
    (D : DeltaStructure p R) (d : R) (a : σ → R) (b : τ → R) :
    DeltaStructure p (SequentialPCompletedDeltaDivision D d a b) :=
  pCompletedDeltaDivisionStructure (pCompletedDeltaDivisionStructure D d a)
    (pCompletedDeltaDivisionMap D d a d) (fun t ↦ pCompletedDeltaDivisionMap D d a (b t))

/-- 元の基底から二段候補への具体的な標準射。 -/
def sequentialPCompletedDeltaDivisionMap
    (D : DeltaStructure p R) (d : R) (a : σ → R) (b : τ → R) :
    R →+* SequentialPCompletedDeltaDivision D d a b :=
  (pCompletedDeltaDivisionMap (pCompletedDeltaDivisionStructure D d a)
    (pCompletedDeltaDivisionMap D d a d)
    (fun t ↦ pCompletedDeltaDivisionMap D d a (b t))).comp (pCompletedDeltaDivisionMap D d a)

/-- 二段候補への標準射はδ射。 -/
theorem sequentialPCompletedDeltaDivisionMap_isDeltaHom
    (D : DeltaStructure p R) (d : R) (a : σ → R) (b : τ → R) :
    D.IsDeltaHom (sequentialPCompletedDeltaDivisionStructure D d a b)
      (sequentialPCompletedDeltaDivisionMap D d a b) :=
  (pCompletedDeltaDivisionMap_isDeltaHom (pCompletedDeltaDivisionStructure D d a)
    (pCompletedDeltaDivisionMap D d a d)
    (fun t ↦ pCompletedDeltaDivisionMap D d a (b t))).comp
      (pCompletedDeltaDivisionMap_isDeltaHom D d a)

set_option maxHeartbeats 800000 in
-- 二段の完備化型と三つの普遍射の型照合に、既定のheartbeat上限を超える。
/-- 一括添加と二段添加の間には、基底射と両立する一意なδ環同型が存在する。 -/
theorem existsUnique_pCompletedDeltaDivisionSequentialEquiv
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R) :
    ∃! e : PCompletedDeltaDivision D d (Sum.elim a b) ≃+*
      SequentialPCompletedDeltaDivision D d a b,
      (pCompletedDeltaDivisionStructure D d (Sum.elim a b)).IsDeltaHom
        (sequentialPCompletedDeltaDivisionStructure D d a b) e.toRingHom ∧
      e.toRingHom.comp (pCompletedDeltaDivisionMap D d (Sum.elim a b)) =
        sequentialPCompletedDeltaDivisionMap D d a b := by
  let D1 := pCompletedDeltaDivisionStructure D d a
  let j1 := pCompletedDeltaDivisionMap D d a
  let d1 := j1 d
  let b1 := fun t ↦ j1 (b t)
  let j2 := pCompletedDeltaDivisionMap D1 d1 b1
  let E2 := sequentialPCompletedDeltaDivisionStructure D d a b
  let c := Sum.elim a b
  let Ec := pCompletedDeltaDivisionStructure D d c
  let jc := pCompletedDeltaDivisionMap D d c
  let := pCompletedDeltaDivision_isAdicComplete D d c
  let := pCompletedDeltaDivision_isAdicComplete D1 d1 b1
  have hE2 : E2.IsPerfect := pCompletedDeltaDivision_isPerfect D1 d1 b1
  have hEc : Ec.IsPerfect := pCompletedDeltaDivision_isPerfect D d c
  have hj1 := pCompletedDeltaDivisionMap_isDeltaHom D d a
  have hd1 : D1.IsDistinguished d1 := hj1.map_isDistinguished hd
  have hdiv (s : σ ⊕ τ) : (j2.comp j1) d ∣ (j2.comp j1) (c s) := by
    cases s with
    | inl s =>
      obtain ⟨x, hx⟩ := pCompletedDeltaDivisionMap_dvd D d a s
      refine ⟨j2 x, ?_⟩
      change j2 (j1 (a s)) = j2 (j1 d) * j2 x
      rw [hx, map_mul]
    | inr t => exact pCompletedDeltaDivisionMap_dvd D1 d1 b1 t
  obtain ⟨f, hf, _⟩ := existsUnique_pCompletedDeltaDivisionHom D E2 hE2 d hd c
    (j2.comp j1) (sequentialPCompletedDeltaDivisionMap_isDeltaHom D d a b) hdiv
  have ha (s : σ) : jc d ∣ jc (a s) := pCompletedDeltaDivisionMap_dvd D d c (Sum.inl s)
  obtain ⟨k, hk, _⟩ := existsUnique_pCompletedDeltaDivisionHom D Ec hEc d hd a jc
    (pCompletedDeltaDivisionMap_isDeltaHom D d c) ha
  have hkval (r : R) : k (j1 r) = jc r := RingHom.congr_fun hk.2 r
  have hb (t : τ) : k d1 ∣ k (b1 t) := by
    change k (j1 d) ∣ k (j1 (b t))
    rw [hkval, hkval]
    exact pCompletedDeltaDivisionMap_dvd D d c (Sum.inr t)
  obtain ⟨g, hg, _⟩ := existsUnique_pCompletedDeltaDivisionHom D1 Ec hEc d1 hd1 b1 k hk.1 hb
  have hgf : g.comp f = RingHom.id (PCompletedDeltaDivision D d c) := by
    apply pCompletedDeltaDivisionHom_ext D Ec hEc d hd c _ _ (hg.1.comp hf.1) Ec.isDeltaHom_id
    change (g.comp f).comp jc = (RingHom.id _).comp jc
    rw [RingHom.comp_assoc, hf.2, ← RingHom.comp_assoc, hg.2, hk.2, RingHom.id_comp]
  have hfk : f.comp k = j2 := by
    apply pCompletedDeltaDivisionHom_ext D E2 hE2 d hd a _ _ (hf.1.comp hk.1)
      (pCompletedDeltaDivisionMap_isDeltaHom D1 d1 b1)
    change (f.comp k).comp j1 = j2.comp j1
    rw [RingHom.comp_assoc, hk.2]
    exact hf.2
  have hfg : f.comp g = RingHom.id (SequentialPCompletedDeltaDivision D d a b) := by
    apply pCompletedDeltaDivisionHom_ext D1 E2 hE2 d1 hd1 b1 _ _ (hf.1.comp hg.1) E2.isDeltaHom_id
    change (f.comp g).comp j2 = (RingHom.id _).comp j2
    rw [RingHom.comp_assoc, hg.2, hfk, RingHom.id_comp]
  have hl : Function.LeftInverse g f := fun x ↦ RingHom.congr_fun hgf x
  have hr : Function.RightInverse g f := fun x ↦ RingHom.congr_fun hfg x
  let e := RingEquiv.ofBijective f ⟨hl.injective, hr.surjective⟩
  refine ⟨e, ⟨hf.1, hf.2⟩, ?_⟩
  intro e' he'
  have h : e'.toRingHom = e.toRingHom := by
    apply pCompletedDeltaDivisionHom_ext D E2 hE2 d hd c _ _ he'.1 hf.1
    exact he'.2.trans hf.2.symm
  apply RingEquiv.ext
  intro x
  exact RingHom.congr_fun h x

end SerrePositivity.BhattScholze
