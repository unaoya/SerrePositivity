module

public import SerrePositivity.BhattScholze.DeltaIdeal
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # δ安定イデアルによる商δ環

BS著者公開版Lemma 2.9とExample 2.10。W₂切断を商へ降下し、
pねじれの有無によらない商δ構造とδ射としての普遍性を構成する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- 環準同型をW₂の各座標に適用する射。商δ構造の切断を降下させるために使う。 -/
def wittTwoMap (f : A →+* B) : WittTwo p A →+* WittTwo p B :=
  RingHom.liftOfRightInverse (WittVector.truncate 2) TruncatedWittVector.out
    TruncatedWittVector.truncateFun_out
    ⟨(WittVector.truncate 2).comp (WittVector.map f), by
      intro x hx
      change (WittVector.truncate 2) (WittVector.map f x) = 0
      apply (WittVector.mem_ker_truncate (p := p) 2 (WittVector.map f x)).mpr
      intro i hi
      rw [WittVector.map_coeff, (WittVector.mem_ker_truncate 2 x).mp hx i hi, map_zero]⟩

/-- W₂上の射は各Witt座標に元の環準同型を適用する。 -/
@[simp] theorem wittTwoMap_coeff (f : A →+* B) (x : WittTwo p A) (i : Fin 2) :
    (wittTwoMap (p := p) f x).coeff i = f (x.coeff i) := by
  change ((WittVector.truncate 2) (WittVector.map f x.out)).coeff i = _
  rw [WittVector.coeff_truncate, WittVector.map_coeff, TruncatedWittVector.coeff_out]

namespace DeltaStructure

/-- δ安定イデアル上では、切断を商のW₂に送った像が零になる。
第0座標は元のイデアル、第1座標はδ安定性を使う。 -/
theorem sectionHom_quotient_eq_zero (D : DeltaStructure p A) (I : Ideal A)
    (hI : D.IsStable I) (x : A) (hx : x ∈ I) :
    ((wittTwoMap (p := p) (Ideal.Quotient.mk I)).comp D.sectionHom) x = 0 := by
  apply TruncatedWittVector.ext
  intro i
  fin_cases i
  · simp only [RingHom.comp_apply, wittTwoMap_coeff,
      TruncatedWittVector.coeff_zero]
    change Ideal.Quotient.mk I ((D.sectionHom x).coeff 0) = 0
    rw [D.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  · simp only [RingHom.comp_apply, wittTwoMap_coeff, TruncatedWittVector.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI x hx)

/-- δ安定イデアルによる商δ構造。切断の環準同型を商の普遍性で降下する。 -/
def quotient (D : DeltaStructure p A) (I : Ideal A) (hI : D.IsStable I) :
    DeltaStructure p (A ⧸ I) where
  sectionHom := Ideal.Quotient.lift I
    ((wittTwoMap (p := p) (Ideal.Quotient.mk I)).comp D.sectionHom)
    (D.sectionHom_quotient_eq_zero I hI)
  coeff_zero := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [Ideal.Quotient.lift_mk, D.coeff_zero]

/-- 商のδは元環のδを標準写像で送ったもの。 -/
@[simp] theorem quotient_delta_mk (D : DeltaStructure p A) (I : Ideal A)
    (hI : D.IsStable I) (x : A) :
    (D.quotient I hI).delta (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (D.delta x) := by
  simp [quotient, delta, Ideal.Quotient.lift_mk]

/-- δ安定商への標準写像はδ射である（BS Lemma 2.9の存在）。 -/
theorem isDeltaHom_quotient_mk (D : DeltaStructure p A) (I : Ideal A) (hI : D.IsStable I) :
    D.IsDeltaHom (D.quotient I hI) (Ideal.Quotient.mk I) := by
  intro x
  exact (D.quotient_delta_mk I hI x).symm

/-- 標準写像と両立する商δ構造は一意。全射性から各元のδを比較する。 -/
theorem quotient_unique (D : DeltaStructure p A) (I : Ideal A) (hI : D.IsStable I)
    (E : DeltaStructure p (A ⧸ I)) (hE : D.IsDeltaHom E (Ideal.Quotient.mk I)) :
    E = D.quotient I hI := by
  apply ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotient_delta_mk, ← hE a]

/-- 商に標準写像と両立するδ構造があるのは、イデアルがδ安定である場合に限る。
存在・一意性をp正則性なしにまとめる（BS著者版Lemma 2.9）。 -/
theorem isStable_iff_existsUnique_quotient (D : DeltaStructure p A) (I : Ideal A) :
    D.IsStable I ↔ ∃! E : DeltaStructure p (A ⧸ I), D.IsDeltaHom E (Ideal.Quotient.mk I) := by
  constructor
  · intro hI
    exact ⟨D.quotient I hI, D.isDeltaHom_quotient_mk I hI,
      fun E hE ↦ D.quotient_unique I hI E hE⟩
  · rintro ⟨E, hE, _⟩
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [hE x, Ideal.Quotient.eq_zero_iff_mem.mpr hx, delta_zero]

/-- Iを零に送るδ射は、δ安定商からの一意なδ射に降下する。
環準同型の商の普遍性とδの標準像上の公式を使う。 -/
theorem existsUnique_quotient_lift (D : DeltaStructure p A) (I : Ideal A)
    (hI : D.IsStable I) (E : DeltaStructure p B) (f : A →+* B)
    (hf : D.IsDeltaHom E f) (hker : I ≤ RingHom.ker f) :
    ∃! g : (A ⧸ I) →+* B,
      g.comp (Ideal.Quotient.mk I) = f ∧ (D.quotient I hI).IsDeltaHom E g := by
  let g := Ideal.Quotient.lift I f (fun x hx ↦ hker hx)
  have hg : g.comp (Ideal.Quotient.mk I) = f := by
    ext x
    rfl
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotient_delta_mk]
    change f (D.delta a) = E.delta (f a)
    exact hf a
  · intro k hk
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (DFunLike.congr_fun hk.1 a).trans (DFunLike.congr_fun hg a).symm

/-- δ閉包で割った商は、Iを零に送るδ射の普遍対象（BS Example 2.10）。
Iそのもののδ安定性は要求しない。 -/
theorem existsUnique_deltaClosure_quotient_lift (D : DeltaStructure p A) (I : Ideal A)
    (E : DeltaStructure p B) (f : A →+* B) (hf : D.IsDeltaHom E f)
    (hker : I ≤ RingHom.ker f) :
    ∃! g : (A ⧸ D.deltaClosure I) →+* B,
      g.comp (Ideal.Quotient.mk (D.deltaClosure I)) = f ∧
        (D.quotient (D.deltaClosure I) (D.isStable_deltaClosure I)).IsDeltaHom E g :=
  D.existsUnique_quotient_lift (D.deltaClosure I) (D.isStable_deltaClosure I)
    E f hf (hf.deltaClosure_le_ker hker)

end DeltaStructure
end SerrePositivity.BhattScholze
