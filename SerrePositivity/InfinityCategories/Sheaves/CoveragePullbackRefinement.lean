module

public import SerrePositivity.InfinityCategories.Sheaves.CoverageUniversalDescent

/-!
概要：Coverage の引き戻しの細分を、同じ係数の指定制限錐とともに保持する。
方針：元の Coverage.pullback の因子分解を生成篩の包含へ移す。
規約：第16項の通常圏での前提計算。大きい引き戻し篩での極限性はまだ結論しない。
  文献対応：HTT 6.2.2.6 の小さい通常の site での被覆生成の入力。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}}

/-- 元の細分の因子分解は、生成した篩の引き戻しへの包含を与える。 -/
lemma coverageRefinement_generate_le {U V : C} (R : Presieve U) (T : Presieve V)
    (f : V ⟶ U) (h : T.FactorsThruAlong R f) :
    Sieve.generate T ≤ (Sieve.generate R).pullback f := by
  rw [Sieve.generate_le_iff]
  intro W g hg
  obtain ⟨Z, i, e, he, hw⟩ := h hg
  change (Sieve.generate R) (g ≫ f)
  rw [← hw]
  exact (Sieve.generate R).downward_closed (Sieve.le_generate R _ _ he) i

/-- 同じ Coverage の細分は、生成被覆で仮定された元の制限錐の極限性も保つ。
細分の選択を全引き戻しの極限性と同一視しない。 -/
lemma coveragePullbackRefinement_isLimit (K : Coverage C) (F : Presheaf C E)
    (hF : ∀ (U : C) (R : Presieve U), R ∈ K.coverings U →
      IsLimitCone (restrictionCone F (Sieve.generate R)))
    {U V : C} (R : Presieve U) (hR : R ∈ K.coverings U) (f : V ⟶ U) :
    ∃ T : Presieve V, T ∈ K.coverings V ∧
      Sieve.generate T ≤ (Sieve.generate R).pullback f ∧
      IsLimitCone (restrictionCone F (Sieve.generate T)) := by
  obtain ⟨T, hT, hfac⟩ := K.pullback f R hR
  exact ⟨T, hT, coverageRefinement_generate_le R T f hfac, hF V T hT⟩

end SerrePositivity.InfinityCategories.Sheaves
