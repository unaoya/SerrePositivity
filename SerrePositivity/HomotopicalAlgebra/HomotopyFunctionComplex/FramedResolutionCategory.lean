module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPrecomposition
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftFunctorLaws

/-! # The category of resolutions with actual outer-frame maps

A morphism records the inner resolution map and an actual outer-frame map.
Composition uses those maps themselves. Fullness of forgetting frames is
proved by ordinary model lifting, without a functorial section assumption.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex

structure FramedResolution (C : Type u) [Category.{v} C] [ModelCategory C] where
  inner : ResolutionObject C

namespace FramedResolution
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

@[ext]
structure Hom (X Y : FramedResolution C) where
  map : X.inner ⟶ Y.inner
  frame : (ResolutionLiftSpace.frame X.inner).obj ⟶ (ResolutionLiftSpace.frame Y.inner).obj
  over : frame ≫ (ResolutionLiftSpace.frame Y.inner).augmentation =
    (ResolutionLiftSpace.frame X.inner).augmentation ≫
      (Functor.const SimplexCategory).map map.diagram

instance : Category (FramedResolution C) where
  Hom := Hom
  id X := ⟨𝟙 _, (ResolutionLiftPrecomposition.identity X.inner).val,
    (ResolutionLiftPrecomposition.identity X.inner).property⟩
  comp f g := ⟨f.map ≫ g.map,
    (ResolutionLiftPrecomposition.compose ⟨f.frame, f.over⟩ ⟨g.frame, g.over⟩).val,
    (ResolutionLiftPrecomposition.compose ⟨f.frame, f.over⟩ ⟨g.frame, g.over⟩).property⟩
  id_comp f := by ext <;> exact Category.id_comp _
  comp_id f := by ext <;> exact Category.comp_id _
  assoc f g h := by ext <;> exact Category.assoc _ _ _

abbrev frameMap {X Y : FramedResolution C} (f : X ⟶ Y) :
    ResolutionLiftPrecomposition.FrameMap f.map := ⟨f.frame, f.over⟩

@[simp]
lemma id_map (X : FramedResolution C) : (𝟙 X : X ⟶ X).map = 𝟙 X.inner := rfl
@[simp]
lemma id_frame (X : FramedResolution C) :
    (𝟙 X : X ⟶ X).frame = 𝟙 (ResolutionLiftSpace.frame X.inner).obj := rfl
@[simp]
lemma comp_map {X Y Z : FramedResolution C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).map = f.map ≫ g.map := rfl
@[simp]
lemma comp_frame {X Y Z : FramedResolution C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).frame = f.frame ≫ g.frame := rfl

/-- The underlying resolution is unchanged. -/
def forget : FramedResolution C ⥤ ResolutionObject C where
  obj X := X.inner
  map f := f.map

/-- Every actual inner morphism admits a frame lift; chosen lifts need not compose. -/
def lift {X Y : FramedResolution C} (f : X.inner ⟶ Y.inner) : X ⟶ Y :=
  ⟨f, (ResolutionLiftPrecomposition.lift f).val, (ResolutionLiftPrecomposition.lift f).property⟩

@[simp]
lemma lift_map {X Y : FramedResolution C} (f : X.inner ⟶ Y.inner) : (lift f).map = f := rfl

instance : (forget (C := C)).Full where
  map_surjective f := ⟨lift f, rfl⟩

abbrev ofResolution (X : ResolutionObject C) : FramedResolution C := ⟨X⟩
abbrev ofObject (X : C) : FramedResolution C := ofResolution (ResolutionObject.ofObject X)

/-- The actual base object and base morphism. -/
abbrev projection : FramedResolution C ⥤ C := forget ⋙ ResolutionObject.projection

/-- Every base morphism lifts between any two framed resolution objects. -/
def liftBase {X Y : FramedResolution C} (f : X.inner.base ⟶ Y.inner.base) : X ⟶ Y :=
  lift (ResolutionObject.lift f)

@[simp]
lemma liftBase_base {X Y : FramedResolution C} (f : X.inner.base ⟶ Y.inner.base) :
    (liftBase f).map.base = f := rfl

instance : (projection (C := C)).Full where
  map_surjective f := ⟨liftBase f, rfl⟩

/-- The outer resolution itself, including its actual maps. -/
def outer : FramedResolution C ⥤ ResolutionObject (SimplexCategory ⥤ C) where
  obj X := ResolutionLiftPrecomposition.outer X.inner
  map f := ⟨f.map.diagram, f.frame, f.over⟩

abbrev innerDiagrams : FramedResolution C ⥤ SimplexCategory ⥤ C :=
  forget ⋙ ResolutionObject.diagrams

abbrev outerDiagrams : FramedResolution C ⥤ SimplexCategory ⥤ SimplexCategory ⥤ C :=
  outer ⋙ ResolutionObject.diagrams

/-- A single strict functor controls all compositions of actual frame maps. -/
def diagonal : FramedResolution C ⥤ SimplexCategory ⥤ C where
  obj X := DiagonalFrame.obj (ResolutionLiftSpace.frame X.inner).obj
  map f := DiagonalFrame.map f.frame
  map_id X := by ext n; rfl
  map_comp f g := by ext n; rfl

/-- The diagonal comparison is natural before applying mapping spaces. -/
def augmentation : diagonal (C := C) ⟶ innerDiagrams where
  app X := DiagonalFrame.augmentation (ResolutionLiftSpace.frame X.inner).augmentation
  naturality {X Y} f := by
    apply NatTrans.ext
    funext n
    exact congr_app (congr_app f.over n) n

end FramedResolution
end SerrePositivity.HomotopyFunctionComplex
