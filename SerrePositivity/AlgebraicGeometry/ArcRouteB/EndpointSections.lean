module

public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Endpoint
public import SerrePositivity.CommutativeAlgebra.ValuationInterval.FinitePresentation

/-!
概要：有限表示代数の剰余体上の点を、左右の非退化な区間の同じ基底上の点へ降ろす。
方針：既存の区間の端点の有向族と、有限表示の因子化を同じ構造射で適用する。
規約：直後・直前の素点がない場合の密度の仮定を明示する。
使われ方：2iのI05・I06、BM18 Proposition 4.8(3),(4)。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

/-- 計画I05：有限表示模型の点を同じ基底上で区間へ因子化する。 -/
theorem exists_right_interval_fp_section
    {V C : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing C] [Algebra V C] [Algebra.FinitePresentation V C]
    (a : PrimeSpectrum V) (hne : ∃ b, a < b)
    (hdense : ∀ b, a < b → ∃ c, a < c ∧ c < b)
    (g : C →ₐ[V] a.asIdeal.ResidueField) :
    ∃ (b : PrimeSpectrum V) (hab : a < b), Nonempty (C →ₐ[V] ValuationIntervalRing hab.le) := by
  classical
  let J := (Set.Ioi a)ᵒᵈ
  letI : Nonempty J := hne.elim (fun b hb ↦ ⟨OrderDual.toDual ⟨b, hb⟩⟩)
  letI : IsDirectedOrder J := ⟨fun j k ↦
    (primeSpectrum_le_total j.ofDual.val k.ofDual.val).elim (fun h ↦ ⟨j, le_rfl, h⟩)
      (fun h ↦ ⟨k, h, le_rfl⟩)⟩
  let lo : J → PrimeSpectrum V := fun _ ↦ a
  let hi : J → PrimeSpectrum V := fun j ↦ j.ofDual.val
  have hlo : Monotone lo := monotone_const
  have hhi : Antitone hi := fun _ _ h ↦ h
  have hh (j : J) : lo j ≤ hi j := j.ofDual.property.le
  have hleft : ∀ x ∈ a.asIdeal, ∃ j : J, x ∈ (lo j).asIdeal :=
    fun _ hx ↦ ⟨Classical.choice inferInstance, hx⟩
  have hright : ∀ x ∉ a.asIdeal, ∃ j : J, x ∉ (hi j).asIdeal := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := exists_primeAbove_not_mem a hne hdense hx
    exact ⟨OrderDual.toDual ⟨b, hb⟩, hxb⟩
  have hcomm : CommRingCat.ofHom (algebraMap V C) ≫ CommRingCat.ofHom g.toRingHom =
      CommRingCat.ofHom (algebraMap V a.asIdeal.ResidueField) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact g.commutes
  obtain ⟨j, r, hr, _⟩ := exists_intervalRingFactor_of_finitePresentation lo hi hlo hhi hh a
    (fun _ ↦ le_rfl) (fun j ↦ j.ofDual.property.le) hleft hright
    (CommRingCat.ofHom (algebraMap V C)) (RingHom.finitePresentation_algebraMap.mpr inferInstance)
    (CommRingCat.ofHom g.toRingHom) hcomm
  refine ⟨j.ofDual.val, j.ofDual.property, ⟨{ r.hom with commutes' := ?_ }⟩⟩
  intro v
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom hr) v

/-- 計画I06：有限表示模型の点を同じ基底上で区間へ因子化する。 -/
theorem exists_left_interval_fp_section
    {V C : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing C] [Algebra V C] [Algebra.FinitePresentation V C]
    (b : PrimeSpectrum V) (hne : ∃ a, a < b)
    (hdense : ∀ a, a < b → ∃ c, a < c ∧ c < b)
    (g : C →ₐ[V] b.asIdeal.ResidueField) :
    ∃ (a : PrimeSpectrum V) (hab : a < b), Nonempty (C →ₐ[V] ValuationIntervalRing hab.le) := by
  classical
  let J := Set.Iio b
  letI : Nonempty J := hne.elim (fun a ha ↦ ⟨⟨a, ha⟩⟩)
  letI : IsDirectedOrder J := ⟨fun j k ↦
    (primeSpectrum_le_total j.val k.val).elim (fun h ↦ ⟨k, h, le_rfl⟩)
      (fun h ↦ ⟨j, le_rfl, h⟩)⟩
  let lo : J → PrimeSpectrum V := fun j ↦ j.val
  let hi : J → PrimeSpectrum V := fun _ ↦ b
  have hlo : Monotone lo := fun _ _ h ↦ h
  have hhi : Antitone hi := antitone_const
  have hh (j : J) : lo j ≤ hi j := j.property.le
  have hleft : ∀ x ∈ b.asIdeal, ∃ j : J, x ∈ (lo j).asIdeal := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := exists_primeBelow_mem b hne hdense hx
    exact ⟨⟨a, ha⟩, hxa⟩
  have hright : ∀ x ∉ b.asIdeal, ∃ j : J, x ∉ (hi j).asIdeal :=
    fun _ hx ↦ ⟨Classical.choice inferInstance, hx⟩
  have hcomm : CommRingCat.ofHom (algebraMap V C) ≫ CommRingCat.ofHom g.toRingHom =
      CommRingCat.ofHom (algebraMap V b.asIdeal.ResidueField) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact g.commutes
  obtain ⟨j, r, hr, _⟩ := exists_intervalRingFactor_of_finitePresentation lo hi hlo hhi hh b
    (fun j ↦ j.property.le) (fun _ ↦ le_rfl) hleft hright
    (CommRingCat.ofHom (algebraMap V C)) (RingHom.finitePresentation_algebraMap.mpr inferInstance)
    (CommRingCat.ofHom g.toRingHom) hcomm
  refine ⟨j.val, j.property, ⟨{ r.hom with commutes' := ?_ }⟩⟩
  intro v
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom hr) v

end SerrePositivity.AlgebraicGeometry.ArcRouteB
