module

public import SerrePositivity.InfinityCategories.Sheaves.LargeGlobalSections
public import SerrePositivity.InfinityCategories.Sheaves.GlobalSectionsSiteFamilyComparison

/-!
概要：元の大きい site の Γ と小さい模型の Γ を、全前層上で同時に比較する。
方針：元の全極限錐族を同じ形状同値で再添字し、二つの定値随伴と比較する。
使われ方：HTT 5.4.7.9、Kerodon §7.1（Tag 02K2）の本質的小さい site の大域切断。
規約：元の全図式・射・高次単体の比較を保持する。係数の宇宙を上げない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type (u + 1)} [Category.{u} C] {D : Type u} [SmallCategory D]
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の大きい全前層の指定極限錐を、同じ coherent な全族として保持する。 -/
def largeGlobalSectionsFamilyData (e : D ≌ C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    {s : LargePresheafCat C E ⟶ (ihom (join (Δ[0] : SSet.{u + 1}) (nerve Cᵒᵖ))).obj E //
      s ≫ coneRestriction (nerve Cᵒᵖ) E = 𝟙 _ ∧
      ∀ v : (LargePresheafCat C E) _⦋0⦌, IsLimitCone (functorVertexCone (s.app _ v))} := by
  let h := exists_pointwiseLimitConeFamily (𝟙 (LargePresheafCat C E))
    (fun v ↦ hasLimit_largePresheaf_of_smallModel e hE (largeVertexToPresheaf v))
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/-- 同じ全錐族の図式への制限は、元の大きい全前層の恒等関手。 -/
lemma largeGlobalSectionsFamilyData_restrict (e : D ≌ C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    (largeGlobalSectionsFamilyData e hE).val ≫ coneRestriction (nerve Cᵒᵖ) E = 𝟙 _ :=
  (largeGlobalSectionsFamilyData e hE).property.1

/-- 同じ全錐族の任意の値は、元の指定大域切断図式の極限。 -/
lemma largeGlobalSectionsFamilyData_isLimit (e : D ≌ C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (v : (LargePresheafCat C E) _⦋0⦌) :
    IsLimitCone (functorVertexCone ((largeGlobalSectionsFamilyData e hE).val.app _ v)) :=
  (largeGlobalSectionsFamilyData e hE).property.2 v

/-- 同じ模型と元の大きい site の Γ の、全前層・全高次単体の比較。 -/
def globalSectionsSmallModelFunctorIso (e : D ≌ C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    FunctorIso (reindexSmallModelPresheafFunctor e E ≫ globalSectionsFunctor hE)
      (largeGlobalSectionsFunctor e hE) := by
  let s := (largeGlobalSectionsFamilyData e hE).val
  let f := (siteSmallModelShapeEquivalence e).hom
  let t := s ≫ (pre (joinMap (𝟙 (Δ[0] : SSet.{u + 1})) f)).app E
  have hs : s ≫ coneRestriction (nerve Cᵒᵖ) E = 𝟙 _ :=
    largeGlobalSectionsFamilyData_restrict e hE
  have ht (v : (LargePresheafCat C E) _⦋0⦌) :
      IsLimitCone (functorVertexCone (t.app _ v)) :=
    (isLimitCone_functorVertexCone_reindex_iff_of_equivalence f
      (siteSmallModelShapeEquivalence e).isQCatEquivalence (s.app _ v)).mpr
        (largeGlobalSectionsFamilyData_isLimit e hE v)
  have ha : t ≫ evaluateFunctorAt (Y := E)
      (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u + 1}) (presheafShape D))) =
      s ≫ evaluateFunctorAt (Y := E)
        (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u + 1}) (nerve Cᵒᵖ))) := by
    dsimp only [t]
    rw [Category.assoc, coneReindex_precomp_apex]
  have hr : t ≫ coneRestriction (presheafShape D) E = reindexSmallModelPresheafFunctor e E := by
    dsimp only [t, reindexSmallModelPresheafFunctor]
    rw [Category.assoc, coneReindex_precomp_restriction, ← Category.assoc, hs, Category.id_comp]
  let a := globalSectionsConeFamilyIso hE t ht
  let b := limitConeFamily_apexIso_of_constantAdjunction (largeGlobalSectionsAdjunction e hE)
    s (largeGlobalSectionsFamilyData_isLimit e hE)
  rw [ha, hr] at a
  rw [hs, Category.id_comp] at b
  exact a.symm ≪≫ b

end SerrePositivity.InfinityCategories.Sheaves
