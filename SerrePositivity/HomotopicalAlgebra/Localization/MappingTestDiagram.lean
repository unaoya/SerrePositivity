module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Accessible

/-! # A fixed family of mapping tests as one arrow in a diagram category

Both endpoints and the precomposition map are actual functors. Their
accessibility is detected pointwise and on the two endpoints of the arrow.
No model category or smallness assertion is required for this construction.
-/

@[expose] public section
universe w t v u vD uD
noncomputable section
open CategoryTheory

namespace SerrePositivity.Bousfield.MappingTestDiagram
variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  {ι : Type t} (F : Cᵒᵖ ⥤ C ⥤ D)

abbrev objects (a : ι → C) : C ⥤ Discrete ι ⥤ D :=
  (Discrete.functor (fun i => F.obj (Opposite.op (a i)))).flip

def precomposition (s : ι → Arrow C) :
    objects F (fun i => (s i).right) ⟶ objects F (fun i => (s i).left) where
  app Y := Discrete.natTrans (fun i => (F.map (s i.as).hom.op).app Y)
  naturality X Y f := by
    apply NatTrans.ext
    funext i
    exact (F.map (s i.as).hom.op).naturality f

def arrow (s : ι → Arrow C) : C ⥤ Arrow (Discrete ι ⥤ D) where
  obj Y := Arrow.mk ((precomposition F s).app Y)
  map f := Arrow.homMk ((objects F (fun i => (s i).right)).map f)
    ((objects F (fun i => (s i).left)).map f) ((precomposition F s).naturality f)
  map_id Y := by ext <;> simp
  map_comp f g := by ext <;> simp

lemma objects_isCardinalAccessible (a : ι → C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ i, (F.obj (Opposite.op (a i))).IsCardinalAccessible κ] :
    (objects F a).IsCardinalAccessible κ := by
  have : ∀ i, Functor.IsCardinalAccessible
      (objects F a ⋙ (evaluation (Discrete ι) D).obj i) κ := fun ⟨i⟩ =>
    inferInstanceAs ((F.obj (Opposite.op (a i))).IsCardinalAccessible κ)
  exact Smith.AccessibleColimits.functorCategory_isCardinalAccessible _ κ

lemma arrow_isCardinalAccessible (s : ι → Arrow C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ i, (F.obj (Opposite.op (s i).left)).IsCardinalAccessible κ]
    [∀ i, (F.obj (Opposite.op (s i).right)).IsCardinalAccessible κ] :
    (arrow F s).IsCardinalAccessible κ := by
  have : (arrow F s ⋙ Arrow.leftFunc).IsCardinalAccessible κ :=
    objects_isCardinalAccessible F (fun i => (s i).right) κ
  have : (arrow F s ⋙ Arrow.rightFunc).IsCardinalAccessible κ :=
    objects_isCardinalAccessible F (fun i => (s i).left) κ
  exact Smith.AccessibleFactorization.arrowFunctor_isCardinalAccessible _ κ

end SerrePositivity.Bousfield.MappingTestDiagram
