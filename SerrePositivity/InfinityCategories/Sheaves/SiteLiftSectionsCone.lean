module

public import SerrePositivity.InfinityCategories.Sheaves.SiteLiftElementsShape
public import SerrePositivity.InfinityCategories.Sheaves.SectionsOf
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentShapeLimitVertex

/-!
概要：元の集合重みの指定切断錐を、同じsiteと値の宇宙表示へ運ぶ。
方針：指定した要素圏の同型の逆で制限し、同じ係数の図式の等式で錐をcastする。
規約：HTT 5.1.5.6、Kerodon §7.1（Tag 02H1）の既存構成の宇宙移送の法則。
  小さい通常のsiteに限る。頂点・全join射・元の射の制限を保持する。
使われ方：5∞-1の残り第11項、任意の係数の元の切断錐で極限性を反映する入力。
-/

@[expose] public noncomputable section
universe u v
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace SerrePositivity.InfinityCategories.Sheaves

/-- 持ち上げ済みのsiteの同じ元の圏の射影で与える切断図式。 -/
abbrev nativeSetSectionsDiagram {D : Type v} [SmallCategory D] {X : SSet.{v}}
    (P : Dᵒᵖ ⥤ Type v) (O : nerve Dᵒᵖ ⟶ X) : nerve P.Elements ⟶ X :=
  nerveMap (Functor.Elements.π P) ≫ O

variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}}

/-- 指定した形状同型の逆は、元の係数を保って同じ図式を移す。 -/
lemma siteLiftSectionsDiagram_eq (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E) :
    (siteLiftElementsShapeIso P).inv ≫ sectionsOfDiagram P O =
      nativeSetSectionsDiagram (siteLiftPresheaf P) ((asSmallSiteShapeIso C).inv ≫ O) := rfl

/-- 元の全錐を、同じ頂点と全join射を保って移す。 -/
def siteLiftSectionsCone (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E)
    (c : JoinCone (sectionsOfDiagram P O)) :
    JoinCone (nativeSetSectionsDiagram (siteLiftPresheaf P) ((asSmallSiteShapeIso C).inv ≫ O)) :=
  (restrictJoinCone c (siteLiftElementsShapeIso P).inv).cast (siteLiftSectionsDiagram_eq P O)

/-- 指定した元の頂点を厳密に保つ。 -/
lemma siteLiftSectionsCone_vertex (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E)
    (c : JoinCone (sectionsOfDiagram P O)) :
    (siteLiftSectionsCone P O c).vertex = c.vertex := by
  rw [siteLiftSectionsCone, JoinCone.vertex_cast, restrictJoinCone_vertex]

/-- 同じ前層の射による錐の制限とも、全join射で可換。 -/
lemma siteLiftSectionsCone_restrict {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (O : Presheaf C E)
    (c : JoinCone (sectionsOfDiagram Q O)) :
    joinMap (𝟙 _) (nerveMap (siteLiftPresheafMap φ).mapElements) ≫
        (siteLiftSectionsCone Q O c).val =
      (siteLiftSectionsCone P O
        (SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.restrictSectionsCone φ O c)).val := by
  have hmap : (siteLiftElementsShapeIso P).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements) =
      nerveMap (siteLiftPresheafMap φ).mapElements ≫ (siteLiftElementsShapeIso Q).inv := by
    apply (cancel_epi (siteLiftElementsShapeIso P).hom).mp
    rw [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, siteLiftElementsShapeIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  change joinMap (𝟙 _) (nerveMap (siteLiftPresheafMap φ).mapElements) ≫
      (joinMap (𝟙 _) (siteLiftElementsShapeIso Q).inv ≫ c.val) =
    joinMap (𝟙 _) (siteLiftElementsShapeIso P).inv ≫
      (joinMap (𝟙 _) ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements)) ≫ c.val)
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp,
    ← Category.assoc, ← joinMap_comp, Category.id_comp, hmap]

/-- 同じ指定錐の極限性は、表示を移しても同値。 -/
lemma siteLiftSectionsCone_isLimit_iff [Quasicategory E]
    (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E) (c : JoinCone (sectionsOfDiagram P O)) :
    IsLimitCone (siteLiftSectionsCone P O c) ↔ IsLimitCone c := by
  have hcast : IsLimitCone (restrictJoinCone c (siteLiftElementsShapeIso P).inv) ↔
      IsLimitCone (siteLiftSectionsCone P O c) :=
    isLimitCone_iff_of_diagram_eq (siteLiftSectionsDiagram_eq P O) rfl
  exact hcast.symm.trans (isLimitCone_iff_restrict_equivalentShape
    (siteLiftElementsShapeIso P).inv (qCatEquivalenceOfIso (siteLiftElementsShapeIso P).symm).isQCatEquivalence c).symm

end SerrePositivity.InfinityCategories.Sheaves
