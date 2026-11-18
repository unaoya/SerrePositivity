module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.CoverageUniversalDescent

/-!
概要：引き戻しで安定な生成被覆篩と前位相の被覆族による層の判定。
方針：実引き戻しを基本生成篩として書き、生成位相の普遍降下判定を使う。
文献対応：HTT 6.2.2.6 の小さい通常の site での特殊化。
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 生成被覆篩の引き戻しが再び基本生成篩なら、その実引き戻しで降下する。 -/
@[cite HTT "6.2.2.6" (partial := special) "小さい通常の site で引き戻しに安定な生成被覆篩。"]
lemma coverage_basis_pullback_isLimit_of_stable
    {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    (K : Coverage C)
    (hstable : ∀ {U V : C} (f : V ⟶ U) (R : Presieve U), R ∈ K.coverings U →
      ∃ T : Presieve V, T ∈ K.coverings V ∧
        Sieve.generate T = (Sieve.generate R).pullback f)
    (F : Presheaf C E)
    (hF : ∀ (U : C) (R : Presieve U), R ∈ K.coverings U →
      IsLimitCone (restrictionCone F (Sieve.generate R)))
    {U V : C} (R : Presieve U) (hR : R ∈ K.coverings U) (f : V ⟶ U) :
    IsLimitCone (restrictionCone F ((Sieve.generate R).pullback f)) := by
  obtain ⟨T, hT, heq⟩ := hstable f R hR
  rw [← heq]
  exact hF V T hT

/-- 引き戻しで安定な基本生成篩での降下は、生成位相での層条件と同値。 -/
@[cite HTT "6.2.2.6" (partial := special) "小さい通常の site で引き戻しに安定な生成被覆篩。"]
lemma isSheaf_toGrothendieck_iff_of_stable
    {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    (K : Coverage C)
    (hstable : ∀ {U V : C} (f : V ⟶ U) (R : Presieve U), R ∈ K.coverings U →
      ∃ T : Presieve V, T ∈ K.coverings V ∧
        Sieve.generate T = (Sieve.generate R).pullback f)
    (F : Presheaf C E) :
    IsSheaf K.toGrothendieck F ↔
      ∀ (U : C) (R : Presieve U), R ∈ K.coverings U →
        IsLimitCone (restrictionCone F (Sieve.generate R)) := by
  rw [isSheaf_toGrothendieck_iff_universallyDescending K F]
  constructor
  · intro h U R hR
    exact (h U R hR).isLimit
  · intro h U R hR V f
    exact coverage_basis_pullback_isLimit_of_stable K hstable F h R hR f

/-- 前位相の被覆族の生成篩での降下は、対応する Grothendieck 位相での層条件と同値。 -/
@[cite HTT "6.2.2.6" (partial := special) "引き戻しを持つ小さい通常の site 上の前位相。"]
lemma isSheaf_pretopology_iff
    {C : Type u} [SmallCategory C] [HasPullbacks C]
    {E : SSet.{u + 1}} [Quasicategory E]
    (J : Pretopology C) (F : Presheaf C E) :
    IsSheaf J.toGrothendieck F ↔
      ∀ (U : C) (R : Presieve U), R ∈ J U →
        IsLimitCone (restrictionCone F (Sieve.generate R)) := by
  have hstable : ∀ {U V : C} (f : V ⟶ U) (R : Presieve U),
      R ∈ J.toCoverage.coverings U →
        ∃ T : Presieve V, T ∈ J.toCoverage.coverings V ∧
          Sieve.generate T = (Sieve.generate R).pullback f := by
    intro U V f R hR
    exact ⟨R.pullbackArrows f, J.pullbacks f R hR, Sieve.pullbackArrows_comm f R⟩
  simpa only [Pretopology.toGrothendieck_toCoverage, Pretopology.mem_toCoverage] using
    isSheaf_toGrothendieck_iff_of_stable J.toCoverage hstable F

end SerrePositivity.InfinityCategories.Sheaves
