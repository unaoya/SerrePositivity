module

public import SerrePositivity.InfinityCategories.Sheaves.SieveIntersectionDescent
public import SerrePositivity.InfinityCategories.Sheaves.TopSieveLimit

/-!
概要：すべての引き戻しで元の制限錐が極限となる篩について、降下の推移性を示す。
方針：元の交叉篩の降下の同値を両順序で適用し、同じ引き戻し篩を比較する。
  文献対応：HTT 6.2.2.6、Kerodon §7.3（Tag 02Y1）の生成位相の層条件。
規約：一つの篩での降下だけから、その全引き戻しの降下を仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}}

/-- 篩の等式は、形状も依存する元の制限錐の極限性を同値として運ぶ。 -/
lemma restrictionCone_isLimit_congr (F : Presheaf C E) {U : C} {S T : Sieve U} (h : S = T) :
    IsLimitCone (restrictionCone F S) ↔ IsLimitCone (restrictionCone F T) := by
  cases h
  rfl

/-- すべての実際の引き戻しで、元の指定制限錐が極限となる篩。 -/
def UniversallyDescendingSieve (F : Presheaf C E) {U : C} (S : Sieve U) : Prop :=
  ∀ ⦃V : C⦄ (f : V ⟶ U), IsLimitCone (restrictionCone F (S.pullback f))

/-- 恒等射への引き戻しで、元の同じ篩の降下を回収する。 -/
lemma UniversallyDescendingSieve.isLimit {F : Presheaf C E} {U : C} {S : Sieve U}
    (h : UniversallyDescendingSieve F S) : IsLimitCone (restrictionCone F S) := by
  exact (restrictionCone_isLimit_congr F (Sieve.pullback_id : S.pullback (𝟙 U) = S)).mp (h (𝟙 U))

/-- 全引き戻しでの降下は、実際の引き戻しに沿って保存される。 -/
lemma UniversallyDescendingSieve.pullback {F : Presheaf C E} {U V : C} {S : Sieve U}
    (h : UniversallyDescendingSieve F S) (f : V ⟶ U) :
    UniversallyDescendingSieve F (S.pullback f) := by
  intro W g
  exact (restrictionCone_isLimit_congr F (Sieve.pullback_comp S)).mp (h (g ≫ f))

variable [Quasicategory E]

/-- 最大篩は、そのすべての引き戻しで元の降下を満たす。 -/
lemma universallyDescendingSieve_top (F : Presheaf C E) (U : C) :
    UniversallyDescendingSieve F (⊤ : Sieve U) := by
  intro V f
  exact (restrictionCone_isLimit_congr F (Sieve.pullback_top (f := f))).mpr
    (topSieveRestrictionCone_isLimit V F)

/-- 元の全引き戻しでの降下は、篩に沿った同じ局所条件で推移的。 -/
lemma UniversallyDescendingSieve.transitive {F : Presheaf C E} {U : C} {R S : Sieve U}
    (hR : UniversallyDescendingSieve F R)
    (hS : ∀ t : sieveCategory R, UniversallyDescendingSieve F (S.pullback t.obj.hom)) :
    UniversallyDescendingSieve F S := by
  intro V f
  have hlocal : ∀ t : sieveCategory (R.pullback f),
      IsLimitCone (restrictionCone F ((S.pullback f).pullback t.obj.hom)) := by
    intro t
    let t' : sieveCategory R := ⟨Over.mk (t.obj.hom ≫ f), t.property⟩
    have h := (hS t').isLimit
    change IsLimitCone (restrictionCone F (S.pullback (t.obj.hom ≫ f))) at h
    exact (restrictionCone_isLimit_congr F (Sieve.pullback_comp S)).mp h
  have hI := (restrictionCone_inf_isLimit_iff_of_pullbacks
    (R.pullback f) (S.pullback f) F hlocal).mpr (hR f)
  apply (restrictionCone_inf_isLimit_iff_of_pullbacks
    (S.pullback f) (R.pullback f) F ?_).mp
  · exact (restrictionCone_isLimit_congr F (inf_comm _ _)).mp hI
  · intro t
    exact (restrictionCone_isLimit_congr F (Sieve.pullback_comp R)).mp (hR (t.obj.hom ≫ f))

end SerrePositivity.InfinityCategories.Sheaves
