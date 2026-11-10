module

public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Colimit
public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Zorn

/-!
概要：剰余体を上下から区間の余極限で近似する（BM18 Proposition 4.8 の証明 (3), (4)）。
方針：素イデアルの鎖の共通部分と合併が素イデアルであることを使う。
規約：上下の添字にそれぞれ直後・直前の素点がない場合を扱う。
使われ方：剰余体の上で得た切断を近傍の非退化区間へ降ろす。
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- 直後の素点を持たない上端の近似（BM18 Proposition 4.8 の証明 (3)）。 -/
theorem exists_primeAbove_not_mem (a : PrimeSpectrum V)
    (hne : ∃ b, a < b) (hdense : ∀ b, a < b → ∃ c, a < c ∧ c < b)
    {x : V} (hx : x ∉ a.asIdeal) :
    ∃ b : PrimeSpectrum V, a < b ∧ x ∉ b.asIdeal := by
  classical
  by_contra! H
  let t := PrimeSpectrum.asIdeal '' Set.Ioi a
  have ht : t.Nonempty := by
    obtain ⟨b, hb⟩ := hne
    exact ⟨b.asIdeal, b, hb, rfl⟩
  have hc : IsChain (· ≤ ·) t := fun p _ q _ _ => le_total p q
  have hP : (sInf t).IsPrime :=
    Ideal.sInf_isPrime_of_isChain ht hc (by rintro _ ⟨b, _, rfl⟩; exact b.isPrime)
  let b : PrimeSpectrum V := ⟨sInf t, hP⟩
  have hab : a ≤ b := by
    change a.asIdeal ≤ sInf t
    apply le_sInf
    rintro _ ⟨c, hc, rfl⟩
    exact (show a < c from hc).le
  have hx' : x ∈ b.asIdeal := by
    change x ∈ sInf t
    rw [Ideal.mem_sInf]
    rintro _ ⟨c, hc, rfl⟩
    exact H c hc
  have hab' : a < b := lt_of_le_of_ne hab (fun he => hx (he.symm ▸ hx'))
  obtain ⟨c, hac, hcb⟩ := hdense b hab'
  exact hcb.not_ge (show sInf t ≤ c.asIdeal from sInf_le ⟨c, hac, rfl⟩)

/-- 直前の素点を持たない下端の近似（BM18 Proposition 4.8 の証明 (4)）。 -/
theorem exists_primeBelow_mem (a : PrimeSpectrum V)
    (hne : ∃ b, b < a) (hdense : ∀ b, b < a → ∃ c, b < c ∧ c < a)
    {x : V} (hx : x ∈ a.asIdeal) :
    ∃ b : PrimeSpectrum V, b < a ∧ x ∈ b.asIdeal := by
  classical
  by_contra! H
  let t := PrimeSpectrum.asIdeal '' Set.Iio a
  have ht : t.Nonempty := by
    obtain ⟨b, hb⟩ := hne
    exact ⟨b.asIdeal, b, hb, rfl⟩
  have hd : DirectedOn (· ≤ ·) t := fun b hb c hc =>
    (le_total b c).elim (fun h => ⟨c, hc, h, le_rfl⟩) (fun h => ⟨b, hb, le_rfl, h⟩)
  have hmem {y : V} : y ∈ sSup t ↔ ∃ I ∈ t, y ∈ I :=
    Submodule.mem_sSup_of_directed ht hd
  have hba : sSup t ≤ a.asIdeal := sSup_le (by
    rintro _ ⟨b, hb, rfl⟩
    exact (show b < a from hb).le)
  have hP : (sSup t).IsPrime :=
    primeSpectrum_asIdeal_sSup_isPrime (Set.Iio a) hne
  let b : PrimeSpectrum V := ⟨sSup t, hP⟩
  have hx' : x ∉ b.asIdeal := by
    intro he
    obtain ⟨I, ⟨c, hc, rfl⟩, hxI⟩ := hmem.mp he
    exact H c hc hxI
  have hba' : b < a := lt_of_le_of_ne hba (fun he => hx' (he.symm ▸ hx))
  obtain ⟨c, hbc, hca⟩ := hdense b hba'
  exact hbc.not_ge (show c.asIdeal ≤ sSup t from le_sSup ⟨c, hca, rfl⟩)

/-- 上から一点に近づく区間族（BM18 Proposition 4.8 の証明 (3)）。 -/
def intervalAboveDiagram (a : PrimeSpectrum V) : (Set.Ioi a)ᵒᵈ ⥤ CommRingCat.{u} :=
  intervalRingDiagram (fun _ => a) (fun j => j.ofDual.val)
    monotone_const (fun _ _ h => h) (fun j => j.ofDual.property.le)

/-- 下から一点に近づく区間族（BM18 Proposition 4.8 の証明 (4)）。 -/
def intervalBelowDiagram (a : PrimeSpectrum V) : Set.Iio a ⥤ CommRingCat.{u} :=
  intervalRingDiagram (fun j => j.val) (fun _ => a)
    (fun _ _ h => h) antitone_const (fun j => j.property.le)

theorem primeSpectrum_le_total (a b : PrimeSpectrum V) : a ≤ b ∨ b ≤ a := by
  classical
  exact le_total a.asIdeal b.asIdeal

/-- 直後の素点がない場合、上側の区間環の filtered 余極限は剰余体
（BM18 Proposition 4.8 の証明 (3)）。 -/
def intervalAboveColimitIsoResidue (a : PrimeSpectrum V)
    (hne : ∃ b, a < b) (hdense : ∀ b, a < b → ∃ c, a < c ∧ c < b)
    [HasColimit (intervalAboveDiagram a)] :
    colimit (intervalAboveDiagram a) ≅ CommRingCat.of a.asIdeal.ResidueField := by
  letI : Nonempty (Set.Ioi a)ᵒᵈ := hne.elim (fun b hb => ⟨OrderDual.toDual ⟨b, hb⟩⟩)
  letI : IsDirectedOrder (Set.Ioi a)ᵒᵈ := ⟨fun j k =>
    (primeSpectrum_le_total j.ofDual.val k.ofDual.val).elim (fun h => ⟨j, le_rfl, h⟩)
      (fun h => ⟨k, h, le_rfl⟩)⟩
  refine intervalRingColimitIsoResidue (J := (Set.Ioi a)ᵒᵈ) (fun _ => a) (fun j => j.ofDual.val)
    monotone_const (fun _ _ h => h) (fun j => j.ofDual.property.le) a
    (fun _ => le_rfl) (fun j => j.ofDual.property.le) ?_ ?_
  · exact fun _ hx => ⟨Classical.choice inferInstance, hx⟩
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := exists_primeAbove_not_mem a hne hdense hx
    exact ⟨OrderDual.toDual ⟨b, hb⟩, hxb⟩

/-- 直前の素点がない場合、下側の区間環の filtered 余極限は剰余体
（BM18 Proposition 4.8 の証明 (4)）。 -/
def intervalBelowColimitIsoResidue (a : PrimeSpectrum V)
    (hne : ∃ b, b < a) (hdense : ∀ b, b < a → ∃ c, b < c ∧ c < a)
    [HasColimit (intervalBelowDiagram a)] :
    colimit (intervalBelowDiagram a) ≅ CommRingCat.of a.asIdeal.ResidueField := by
  letI : Nonempty (Set.Iio a) := hne.elim (fun b hb => ⟨⟨b, hb⟩⟩)
  letI : IsDirectedOrder (Set.Iio a) := ⟨fun j k =>
    (primeSpectrum_le_total j.val k.val).elim (fun h => ⟨k, h, le_rfl⟩)
      (fun h => ⟨j, le_rfl, h⟩)⟩
  refine intervalRingColimitIsoResidue (J := Set.Iio a) (fun j => j.val) (fun _ => a)
    (fun _ _ h => h) antitone_const (fun j => j.property.le) a
    (fun j => j.property.le) (fun _ => le_rfl) ?_ ?_
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := exists_primeBelow_mem a hne hdense hx
    exact ⟨⟨b, hb⟩, hxb⟩
  · exact fun _ hx => ⟨Classical.choice inferInstance, hx⟩

end SerrePositivity
