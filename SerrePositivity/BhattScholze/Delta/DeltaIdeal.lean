module

public import SerrePositivity.BhattScholze.Delta.DeltaRing

/-! # δ安定イデアルの閉包

BS著者版Example 2.10のδ安定化を、元のイデアルを含むδ安定イデアルの
交わりとして構成する。商環のδ構造の構成とは独立な、最小性の部分を証明する。
-/

@[expose] public noncomputable section

universe u v
namespace SerrePositivity.BhattScholze.DeltaStructure

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- δ安定イデアルの逆像はδ安定。δ射の可換性を使い、商の普遍性に備える。 -/
theorem IsDeltaHom.isStable_comap {B : Type v} [CommRing B]
    {D : DeltaStructure p A} {E : DeltaStructure p B} {f : A →+* B}
    (hf : D.IsDeltaHom E f) {J : Ideal B} (hJ : E.IsStable J) :
    D.IsStable (J.comap f) := by
  intro x hx
  change f (D.delta x) ∈ J
  rw [hf x]
  exact hJ (f x) hx

/-- δ閉包：Iを含むすべてのδ安定イデアルの交わり。
余分な正則性・完備性を要求せず、δ環の商構成に用いる（BS Example 2.10）。 -/
def deltaClosure (D : DeltaStructure p A) (I : Ideal A) : Ideal A :=
  sInf {J : Ideal A | I ≤ J ∧ D.IsStable J}

/-- 元がδ閉包に属するのは、Iを含むすべてのδ安定イデアルに属するとき。 -/
theorem mem_deltaClosure (D : DeltaStructure p A) (I : Ideal A) (x : A) :
    x ∈ D.deltaClosure I ↔ ∀ J : Ideal A, I ≤ J → D.IsStable J → x ∈ J := by
  simp [deltaClosure, Submodule.mem_sInf]

/-- 元のイデアルはそのδ閉包に含まれる。 -/
theorem le_deltaClosure (D : DeltaStructure p A) (I : Ideal A) : I ≤ D.deltaClosure I := by
  intro x hx
  rw [mem_deltaClosure]
  exact fun J hIJ _ ↦ hIJ hx

/-- δ閉包はδで安定。交わりを取る各イデアルのδ安定性を使う。 -/
theorem isStable_deltaClosure (D : DeltaStructure p A) (I : Ideal A) :
    D.IsStable (D.deltaClosure I) := by
  intro x hx
  rw [mem_deltaClosure] at hx ⊢
  intro J hIJ hJ
  exact hJ x (hx J hIJ hJ)

/-- δ閉包はIを含むδ安定イデアルの中で最小。商を経由する射の構成に使う。 -/
theorem deltaClosure_le (D : DeltaStructure p A) {I J : Ideal A}
    (hIJ : I ≤ J) (hJ : D.IsStable J) : D.deltaClosure I ≤ J := by
  intro x hx
  exact (D.mem_deltaClosure I x).mp hx J hIJ hJ

/-- δで安定なイデアルのδ閉包は元のイデアル。 -/
theorem deltaClosure_eq (D : DeltaStructure p A) {I : Ideal A} (hI : D.IsStable I) :
    D.deltaClosure I = I :=
  le_antisymm (D.deltaClosure_le le_rfl hI) (D.le_deltaClosure I)

/-- δ閉包はイデアルの包含に関して単調。 -/
theorem deltaClosure_mono (D : DeltaStructure p A) {I J : Ideal A} (hIJ : I ≤ J) :
    D.deltaClosure I ≤ D.deltaClosure J :=
  D.deltaClosure_le (hIJ.trans (D.le_deltaClosure J)) (D.isStable_deltaClosure J)

/-- δ閉包を二度取っても変わらない。 -/
@[simp] theorem deltaClosure_idempotent (D : DeltaStructure p A) (I : Ideal A) :
    D.deltaClosure (D.deltaClosure I) = D.deltaClosure I :=
  D.deltaClosure_eq (D.isStable_deltaClosure I)

/-- δ射がIを零に送れば、そのδ閉包も零に送る。
核のδ安定性と最小性により、δ安定商の普遍性の核条件を得る。 -/
theorem IsDeltaHom.deltaClosure_le_ker {B : Type v} [CommRing B]
    {D : DeltaStructure p A} {E : DeltaStructure p B} {f : A →+* B}
    (hf : D.IsDeltaHom E f) {I : Ideal A} (hI : I ≤ RingHom.ker f) :
    D.deltaClosure I ≤ RingHom.ker f :=
  D.deltaClosure_le hI hf.isStable_ker

end SerrePositivity.BhattScholze.DeltaStructure
