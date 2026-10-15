module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryDiagramIso
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionFunctor

/-! # Naturally recovering attaching data from its actual extended functor

Both construction and recovery act on morphisms, and their composite is
naturally isomorphic to the original attaching diagram. Consequently the
comparison also applies to arrows and commutative squares of attaching data.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy.BoundaryDiagram
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J) (C : Type u') [Category.{v'} C]

abbrev toAdjoinFunctor : BoundaryDiagram r j C ⥤ (Adjoin r j ⥤ C) where
  obj D := D.extension.toFunctor
  map m := m.upper.toNatTrans
  map_id D := by ext x; cases x <;> rfl
  map_comp m n := by ext x; cases x <;> rfl

abbrev fromAdjoinFunctor : (Adjoin r j ⥤ C) ⥤ BoundaryDiagram r j C where
  obj F :=
    { lower := adjoinLower r j ⋙ F
      extension :=
        { obj := F.obj none
          incoming {x} f _ := F.map (InducedCategory.homMk (X := some x) (Y := none) f)
          outgoing {x} f _ := F.map (InducedCategory.homMk (X := none) (Y := some x) f)
          incoming_naturality f g _ _ := (F.map_comp _ _).symm
          outgoing_naturality f g _ _ := (F.map_comp _ _).symm
          crossing f g _ _ := (F.map_comp _ _).symm } }
  map τ :=
    { lower := Functor.whiskerLeft (adjoinLower r j) τ
      upper :=
        { hom := τ.app none
          incoming {x} f _ := τ.naturality (InducedCategory.homMk (X := some x) (Y := none) f)
          outgoing {x} f _ := τ.naturality (InducedCategory.homMk (X := none) (Y := some x) f) } }
  map_id F := by apply Hom.ext <;> rfl
  map_comp τ σ := by apply Hom.ext <;> rfl

abbrev reconstructionIsoApp (D : BoundaryDiagram r j C) :
    (fromAdjoinFunctor r j C).obj ((toAdjoinFunctor r j C).obj D) ≅ D :=
  isoMk D.extension.restrictionIso (Iso.refl _) (by
    intro x f hf
    change D.extension.toFunctor.map (InducedCategory.homMk (X := some x) (Y := none) f) ≫
        𝟙 D.extension.obj = 𝟙 (D.lower.obj x) ≫ D.extension.incoming f hf
    rw [D.extension.toFunctor_map_incoming f hf]
    exact (Category.comp_id _).trans (Category.id_comp _).symm) (by
    intro x f hf
    change D.extension.toFunctor.map (InducedCategory.homMk (X := none) (Y := some x) f) ≫
        𝟙 (D.lower.obj x) = 𝟙 D.extension.obj ≫ D.extension.outgoing f hf
    rw [D.extension.toFunctor_map_outgoing f hf]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

def reconstructionIso : toAdjoinFunctor r j C ⋙ fromAdjoinFunctor r j C ≅ 𝟭 _ :=
  NatIso.ofComponents (reconstructionIsoApp r j C) (fun {D E} m ↦ by
    apply Hom.ext
    · ext x
      change m.upper.toNatTrans.app (some x) ≫ 𝟙 (E.lower.obj x) =
        𝟙 (D.lower.obj x) ≫ m.lower.app x
      change m.lower.app x ≫ 𝟙 (E.lower.obj x) = 𝟙 (D.lower.obj x) ≫ m.lower.app x
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    · change m.upper.hom ≫ 𝟙 E.extension.obj = 𝟙 D.extension.obj ≫ m.upper.hom
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

end SerrePositivity.Reedy.BoundaryDiagram
