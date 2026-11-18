module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.NativeSiteDescent
public import SerrePositivity.InfinityCategories.Sheaves.CoveragePullbackRefinement

/-!
概要：Coverage の局所細分は、元の引き戻し篩の中に指定された極限錐を与える。
方針：元の篩の所属証明と指定された制限錐を保つ。
  文献対応：HTT 6.2.2.6、通常の小さい site の Coverage の場合。
使われ方：生成篩からの降下の判定。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

namespace SerrePositivity.InfinityCategories.Sheaves

/-- Coverage の局所細分は、元の引き戻し篩の中に指定された極限錐を与える。 -/
@[cite HTT "6.2.2.6" (partial := special) "小さい通常の site の Coverage の篩の比較。"]
lemma coverageLocalRefinement_for_generatedSieve :
∀ {C : Type u} [SmallCategory C] {E : SSet.{u}} [Quasicategory E]
 (K : Coverage C) (F : nerve Cᵒᵖ ⟶ E)
 (hF : ∀ (U : C) (R : Presieve U), R ∈ K.coverings U →
   IsLimitCone (nativeRestrictionCone F (Sieve.generate R))),
∀ {U : C} (R : Presieve U) (hR : R ∈ K.coverings U)
 (S : Sieve U) (hS : Sieve.generate R ≤ S) (t : sieveCategory S),
 ∃ T : Presieve t.obj.left, T ∈ K.coverings t.obj.left ∧
   Sieve.generate T ≤ (Sieve.generate R).pullback t.obj.hom ∧
   IsLimitCone (nativeRestrictionCone F (Sieve.generate T)) := by
  intro C hC E hE K F hF U R hR S hS t
  obtain ⟨T, hT, hfac⟩ := K.pullback t.obj.hom R hR
  exact ⟨T, hT, coverageRefinement_generate_le R T t.obj.hom hfac, hF _ T hT⟩

end SerrePositivity.InfinityCategories.Sheaves
