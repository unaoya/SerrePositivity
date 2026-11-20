module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedParameterCylinderHom

/-!
概要：パラメータ付き円柱の豊穣圏の法則。
方針：端の組を分け、元の Hom の単位律・結合律を各単体で計算する。
規約：パラメータの Kan 性は不要。使われ方：評価の coherent な円柱への移送。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder
end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory
open _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder
variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- 元の左単位律を単体で評価した式。 -/
lemma base_id_comp_app (X Y : C) (d : SimplexCategoryᵒᵖ) (a : (X ⟶[SSet] Y).obj d) :
    (eComp SSet X X Y).app d ((eId SSet X).app d PUnit.unit, a) = a :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (e_id_comp SSet X Y) d) a

/-- 元の右単位律を単体で評価した式。 -/
lemma base_comp_id_app (X Y : C) (d : SimplexCategoryᵒᵖ) (a : (X ⟶[SSet] Y).obj d) :
    (eComp SSet X Y Y).app d (a, (eId SSet Y).app d PUnit.unit) = a :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (e_comp_id SSet X Y) d) a

/-- 元の結合律を三つの単体で評価した式。 -/
lemma base_assoc_app (W X Y Z : C) (d : SimplexCategoryᵒᵖ)
    (a : (W ⟶[SSet] X).obj d) (b : (X ⟶[SSet] Y).obj d) (c : (Y ⟶[SSet] Z).obj d) :
    (eComp SSet W Y Z).app d ((eComp SSet W X Y).app d (a, b), c) =
      (eComp SSet W X Z).app d (a, (eComp SSet X Y Z).app d (b, c)) := by
  let abc : ((W ⟶[SSet] X) ⊗ ((X ⟶[SSet] Y) ⊗ (Y ⟶[SSet] Z))).obj d := (a, (b, c))
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (e_assoc SSet W X Y Z) d) abc
  exact h

variable (A : SSet.{u})

/-- 円柱の左単位律。 -/
lemma identity_composition (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) :
    (λ_ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A X Y)).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.identity A X ▷ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.composition A X X Y = 𝟙 _ := by
  rcases X with ⟨s, x⟩
  rcases Y with ⟨t, y⟩
  cases s <;> cases t
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
  · exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_id_comp_app x y d a
  · exact Prod.ext rfl (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_id_comp_app x y d a.2)
  · exact a.elim
  · exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_id_comp_app x y d a

/-- 円柱の右単位律。 -/
lemma composition_identity (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) :
    (ρ_ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A X Y)).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A X Y ◁ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.identity A Y ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.composition A X Y Y = 𝟙 _ := by
  rcases X with ⟨s, x⟩
  rcases Y with ⟨t, y⟩
  cases s <;> cases t
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
  · exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_comp_id_app x y d a
  · exact Prod.ext rfl (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_comp_id_app x y d a.2)
  · exact a.elim
  · exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_comp_id_app x y d a

/-- 円柱の結合律。 -/
lemma composition_assoc (W X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) :
    (α_ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A W X) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A X Y) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A Y Z)).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.composition A W X Y ▷ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A Y Z ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.composition A W Y Z =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A W X ◁ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.composition A X Y Z ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.composition A W X Z := by
  rcases W with ⟨s, w⟩
  rcases X with ⟨t, x⟩
  rcases Y with ⟨r, y⟩
  rcases Z with ⟨q, z⟩
  cases s <;> cases t <;> cases r <;> cases q
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨a, b, c⟩
  · exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app w x y z d a b c
  · exact Prod.ext rfl (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app w x y z d a b c.2)
  · exact c.elim
  · exact Prod.ext rfl (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app w x y z d a b.2 c)
  · exact b.elim
  · exact b.elim
  · exact c.elim
  · exact Prod.ext rfl (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app w x y z d a.2 b c)
  · exact a.elim
  · exact a.elim
  · exact a.elim
  · exact a.elim
  · exact b.elim
  · exact b.elim
  · exact c.elim
  · exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app w x y z d a b c

/-- 円柱の実際の単体集合による豊穣構造。 -/
instance enrichedCategory : EnrichedCategory SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) where
  Hom := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A
  id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.identity A
  comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.composition A
  id_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.identity_composition A
  comp_id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.composition_identity A
  assoc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.composition_assoc A

/-- 単位からの射を通常の射とする円柱の圏。 -/
instance category : Category.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) :=
  inferInstanceAs (Category (ForgetEnrichment SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C)))

/-- 円柱の通常の射と豊穣射は元の単位からの対応を持つ。 -/
instance simplicialCategory : SimplicialCategory (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) where
  homEquiv := Equiv.refl _
  homEquiv_id X := ForgetEnrichment.homTo_id (W := SSet.{u}) (C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) X
  homEquiv_comp f g := ForgetEnrichment.homTo_comp (W := SSet.{u}) (C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) f g

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
