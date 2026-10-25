module

public import SerrePositivity.BhattScholze.Prism.Residue.PrismaticCoefficientQuotientComposition

/-! # prism係数の冪剰余と冪零厚化

A/(a,dⁿ)からA/(a,d)への具体的な冪零商。n>0の標準射を固定する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {A : Type u} [CommRing A] (a d : A) (n : ℕ)
local notation "Jₙ" => Ideal.span (Set.insert a (Set.singleton (d ^ n)))
local notation "J₁" => Ideal.span (Set.insert a (Set.singleton d))
local notation "Tₙ" => A ⧸ Jₙ
local notation "qₙ" => Ideal.Quotient.mk Jₙ
local notation "q₁" => Ideal.Quotient.mk J₁

/-- 冪剰余A/(a,dⁿ)の中でdの像が生成するイデアル。 -/
def prismaticPowerResidueIdeal : Ideal Tₙ := Ideal.span {qₙ d}

/-- dの像の主イデアルはn乗で零。n=0の零環も含む。 -/
theorem prismaticPowerResidueIdeal_pow :
    prismaticPowerResidueIdeal a d n ^ n = ⊥ := by
  have hd : qₙ d ^ n = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  rw [prismaticPowerResidueIdeal, Ideal.span_singleton_pow, hd]
  simp

/-- 正の冪について、二生成イデアル(a,dⁿ)は(a,d)に含まれる。 -/
theorem prismaticPowerResidue_sourceIdeal_le (hn : 0 < n) : Jₙ ≤ J₁ := by
  apply Ideal.span_le.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact Ideal.subset_span (Set.mem_insert _ _)
  · obtain rfl := Set.mem_singleton_iff.mp hx
    exact Ideal.pow_mem_of_mem _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))) n hn

/-- 正の冪剰余から一乗剰余への標準環射。 -/
def prismaticPowerResidueMap (hn : 0 < n) : Tₙ →+* A ⧸ J₁ :=
  Ideal.quotientMap J₁ (RingHom.id A) (by
    intro x hx
    exact prismaticPowerResidue_sourceIdeal_le a d n hn hx)

/-- 標準射の合成は元のAからの(a,d)商射そのもの。 -/
theorem prismaticPowerResidueMap_comp (hn : 0 < n) :
    (prismaticPowerResidueMap a d n hn).comp qₙ = q₁ := rfl

/-- 冪剰余から一乗剰余への標準射は全射。 -/
theorem prismaticPowerResidueMap_surjective (hn : 0 < n) :
    Function.Surjective (prismaticPowerResidueMap a d n hn) :=
  Ideal.quotientMap_surjective Function.surjective_id

/-- (a,d)の冪剰余への像はdの像の主イデアルである。 -/
theorem prismaticPowerResidueIdeal_eq_map :
    (J₁).map qₙ = prismaticPowerResidueIdeal a d n := by
  have ha : qₙ a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_insert _ _))
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      change qₙ a ∈ prismaticPowerResidueIdeal a d n
      rw [ha]
      exact Ideal.zero_mem _
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact Ideal.subset_span (Set.mem_singleton _)
  · apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact Ideal.mem_map_of_mem qₙ
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- 標準全射の核は具体的な冪零イデアルKₙである。 -/
theorem prismaticPowerResidueMap_ker (hn : 0 < n) :
    RingHom.ker (prismaticPowerResidueMap a d n hn) =
      prismaticPowerResidueIdeal a d n := by
  rw [prismaticPowerResidueMap, Ideal.quotientMap, Ideal.ker_quotient_lift]
  simpa only [RingHom.comp_id, Ideal.mk_ker] using prismaticPowerResidueIdeal_eq_map a d n

/-- Kₙでさらに商を取ると、標準写像に沿ってA/(a,d)を得る。 -/
def prismaticPowerResidueQuotientEquiv (hn : 0 < n) :
    Tₙ ⧸ prismaticPowerResidueIdeal a d n ≃+* A ⧸ J₁ :=
  (Ideal.quotEquivOfEq (prismaticPowerResidueMap_ker a d n hn).symm).trans
    (RingHom.quotientKerEquivOfSurjective (prismaticPowerResidueMap_surjective a d n hn))

/-- 冪零商の同型は、具体的な標準全射を保つ。 -/
theorem prismaticPowerResidueQuotientEquiv_comp_mk (hn : 0 < n) :
    (prismaticPowerResidueQuotientEquiv a d n hn).toRingHom.comp
        (Ideal.Quotient.mk (prismaticPowerResidueIdeal a d n)) =
      prismaticPowerResidueMap a d n hn := by
  apply RingHom.ext
  intro x
  rfl

end SerrePositivity.BhattScholze
