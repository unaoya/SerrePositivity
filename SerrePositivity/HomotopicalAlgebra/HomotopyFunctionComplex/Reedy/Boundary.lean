module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Degree
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects

/-! # The boundary map determined by a lower-degree diagram

An incoming direct map a ⟶ j followed by an outgoing inverse map j ⟶ b
has both endpoints below deg j. The given lower-degree diagram can therefore
be evaluated on their composite, without assigning an object at j. These
maps determine the actual boundary comparison from the latching colimit to
the matching limit used for a Reedy extension step.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)

abbrev crossing (f : LatchingIndex r j) (g : MatchingIndex r j) :
    (latchingSourceLower r j).obj f ⟶ (matchingTargetLower r j).obj g :=
  ObjectProperty.homMk (f.obj.hom ≫ g.obj.hom)

lemma crossing_left {f f' : LatchingIndex r j} (φ : f ⟶ f') (g : MatchingIndex r j) :
    (latchingSourceLower r j).map φ ≫ crossing r j f' g = crossing r j f g := by
  apply ObjectProperty.hom_ext
  change φ.hom.left ≫ (f'.obj.hom ≫ g.obj.hom) = f.obj.hom ≫ g.obj.hom
  rw [← Category.assoc, Over.w]

lemma crossing_right (f : LatchingIndex r j) {g g' : MatchingIndex r j} (ψ : g ⟶ g') :
    crossing r j f g ≫ (matchingTargetLower r j).map ψ = crossing r j f g' := by
  apply ObjectProperty.hom_ext
  change (f.obj.hom ≫ g.obj.hom) ≫ ψ.hom.right = f.obj.hom ≫ g'.obj.hom
  rw [Category.assoc, Under.w]

variable {C : Type u'} [Category.{v'} C] (H : Lower r (r.deg j) ⥤ C)

abbrev lowerLatchingCocone (g : MatchingIndex r j) :
    Cocone (latchingSourceLower r j ⋙ H) where
  pt := H.obj ((matchingTargetLower r j).obj g)
  ι :=
    { app f := H.map (crossing r j f g)
      naturality f f' φ := by
        change H.map ((latchingSourceLower r j).map φ) ≫ H.map (crossing r j f' g) =
          H.map (crossing r j f g) ≫ 𝟙 _
        rw [← H.map_comp, crossing_left, Category.comp_id] }

variable [HasColimitsOfShape (LatchingIndex r j) C]

lemma lowerLatchingDesc_naturality {g g' : MatchingIndex r j} (ψ : g ⟶ g') :
    colimit.desc _ (lowerLatchingCocone r j H g) ≫ H.map ((matchingTargetLower r j).map ψ) =
      colimit.desc _ (lowerLatchingCocone r j H g') := by
  apply colimit.hom_ext
  intro f
  rw [colimit.ι_desc_assoc, colimit.ι_desc]
  change H.map (crossing r j f g) ≫ H.map ((matchingTargetLower r j).map ψ) =
    H.map (crossing r j f g')
  rw [← H.map_comp, crossing_right]

abbrev lowerBoundaryCone : Cone (matchingTargetLower r j ⋙ H) where
  pt := colimit (latchingSourceLower r j ⋙ H)
  π :=
    { app g := colimit.desc _ (lowerLatchingCocone r j H g)
      naturality g g' ψ := by
        change 𝟙 _ ≫ colimit.desc _ (lowerLatchingCocone r j H g') =
          colimit.desc _ (lowerLatchingCocone r j H g) ≫ H.map ((matchingTargetLower r j).map ψ)
        rw [Category.id_comp]
        exact (lowerLatchingDesc_naturality r j H ψ).symm }

variable [HasLimitsOfShape (MatchingIndex r j) C]

abbrev lowerBoundary : colimit (latchingSourceLower r j ⋙ H) ⟶
    limit (matchingTargetLower r j ⋙ H) := limit.lift _ (lowerBoundaryCone r j H)

@[reassoc (attr := simp)]
lemma ι_lowerBoundary_π (f : LatchingIndex r j) (g : MatchingIndex r j) :
    colimit.ι (latchingSourceLower r j ⋙ H) f ≫ lowerBoundary r j H ≫
      limit.π (matchingTargetLower r j ⋙ H) g = H.map (crossing r j f g) := by
  rw [limit.lift_π, colimit.ι_desc]

end SerrePositivity.Reedy
