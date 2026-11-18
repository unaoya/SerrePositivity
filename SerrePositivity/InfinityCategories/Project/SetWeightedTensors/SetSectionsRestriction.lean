module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality

/-!
概要：集合重みの射に沿う既存の切断錐の制限を、同じ slice の全関手として表示する。
方針：既存の sliceOverRestrict と、元の係数図式の等式での移送を合成する。
規約：HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）の既存構成の自然性・合成則の入力。
使われ方：S8 の指定切断射の合成の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight
variable {I : Type u} [SmallCategory I] {P Q : I ⥤ Type u}
variable {E : SSet.{u + 1}} (φ : P ⟶ Q)
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)

/-- 係数図式の等式による slice の移送は、元の全射を保持する。 -/
lemma sliceOver_diagramEq_val {K X : SSet.{u + 1}} {p q : K ⟶ X} (h : p = q)
    (n : SimplexCategoryᵒᵖ) (s : (sliceOver p).obj n) :
    ((eqToHom (congrArg sliceOver h)).app n s).val = s.val := by
  cases h
  rfl

/-- 元の切断錐の制限は、同じ係数図式上の slice の関手。 -/
def restrictSectionsFunctor : sliceOver (diagram Q F) ⟶ sliceOver (diagram P F) :=
  sliceOverRestrict (diagram Q F) (elementsMap φ) ≫
    eqToHom (congrArg sliceOver (elementsMap_diagram φ F))

/-- すべての次数で、制限は同じ重みの射の join による前合成。 -/
lemma restrictSectionsFunctor_val (n : SimplexCategoryᵒᵖ) (s : (sliceOver (diagram Q F)).obj n) :
    ((restrictSectionsFunctor φ F).app n s).val =
      joinMap (𝟙 _) (elementsMap φ) ≫ s.val := by
  change ((eqToHom (congrArg sliceOver (elementsMap_diagram φ F))).app n
    ((sliceOverRestrict (diagram Q F) (elementsMap φ)).app n s)).val = _
  rw [sliceOver_diagramEq_val (elementsMap_diagram φ F)]
  rfl

/-- 全関手の零次成分は、既存の同じ指定切断錐の制限。 -/
lemma restrictSectionsFunctor_vertex (c : JoinCone (diagram Q F)) :
    (restrictSectionsFunctor φ F).app (Opposite.op ⦋0⦌) c = restrictSectionsCone φ F c := by
  apply Subtype.ext
  exact restrictSectionsFunctor_val φ F _ c

/-- 制限は全次数で元の錐の頂点側の射影を保つ。 -/
lemma restrictSectionsFunctor_projection :
    restrictSectionsFunctor φ F ≫ sliceOverProjection (diagram P F) =
      sliceOverProjection (diagram Q F) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (joinInl Δ[n.unop.len] _ ≫
    ((restrictSectionsFunctor φ F).app n s).val) =
      SSet.yonedaEquiv (joinInl Δ[n.unop.len] _ ≫ s.val)
  rw [restrictSectionsFunctor_val, ← Category.assoc, joinInl_joinMap, Category.id_comp]

/-- 元の圏の比較射は、集合重みの合成と同じ順序で合成する。 -/
lemma elementsMap_comp {R : I ⥤ Type u} (ψ : Q ⟶ R) :
    elementsMap (φ ≫ ψ) = elementsMap φ ≫ elementsMap ψ := rfl

/-- 二段の制限は、元の同じ指定錐の合成した制限に厳密に一致する。 -/
lemma restrictSectionsCone_comp {R : I ⥤ Type u} (ψ : Q ⟶ R)
    (c : JoinCone (diagram R F)) :
    restrictSectionsCone φ F (restrictSectionsCone ψ F c) =
      restrictSectionsCone (φ ≫ ψ) F c := by
  apply Subtype.ext
  change joinMap (𝟙 _) (elementsMap φ) ≫ (joinMap (𝟙 _) (elementsMap ψ) ≫ c.val) =
    joinMap (𝟙 _) (elementsMap (φ ≫ ψ)) ≫ c.val
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp, ← elementsMap_comp]

/-- 全関手としての二段の制限も、同じ重みの合成に一致する。 -/
lemma restrictSectionsFunctor_comp {R : I ⥤ Type u} (ψ : Q ⟶ R) :
    restrictSectionsFunctor (φ ≫ ψ) F =
      restrictSectionsFunctor ψ F ≫ restrictSectionsFunctor φ F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  simp only [NatTrans.comp_app_apply, restrictSectionsFunctor_val]
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp, ← elementsMap_comp]

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight
