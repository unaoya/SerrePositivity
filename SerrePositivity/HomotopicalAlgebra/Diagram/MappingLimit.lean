module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHom
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # The actual diagram Hom as a limit of evaluated simplicial Hom

The limit cone and its universal maps are explicit. The index and source
Hom universes may differ, so pointwise values are lifted to their maximum.
This is an ordinary limit theorem, not by itself a homotopy-limit theorem.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits ConcreteCategory


namespace SerrePositivity.DiagramModel.MappingLimit
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  (A : SimplexCategory ⥤ K ⥤ C) (Y : C)

abbrev pointwise : Kᵒᵖ ⥤ SSet.{v} :=
  A.flip.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor.flip.obj Y

abbrev lifted : Kᵒᵖ ⥤ SSet.{max w v} := pointwise K A Y ⋙ SSet.uliftFunctor.{w,v}

abbrev diagramHom : SSet.{max w v} :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj ((Functor.const K).obj Y)

/-- Evaluation at k sends a diagram natural transformation to its k-component. -/
def cone : Cone (lifted K A Y) where
  pt := diagramHom K A Y
  π := {
    app k := {
      app n := ↾fun a => ULift.up (a.app k.unop)
      naturality n m f := by
        ext a
        rfl }
    naturality k l f := by
      ext n a
      apply ULift.ext
      have h := a.naturality f.unop
      exact (h.trans (Category.comp_id _)).symm }

/-- The universal simplicial map is the actual family of natural transformations. -/
def coneIsLimit : IsLimit (cone K A Y) where
  lift s := {
    app n := ↾fun z => {
      app k := ((s.π.app (Opposite.op k)).app n z).down
      naturality k l f := by
        have h := congr_hom (congr_app (s.π.naturality f.op) n) z
        change ((A.obj n.unop).map f ≫ ((s.π.app (Opposite.op l)).app n z).down) =
          ((s.π.app (Opposite.op k)).app n z).down ≫ 𝟙 Y
        exact (congrArg ULift.down h).symm.trans (Category.comp_id _).symm }
    naturality n m f := by
      ext z
      apply NatTrans.ext
      funext k
      have h := congr_hom ((s.π.app (Opposite.op k)).naturality f) z
      exact congrArg ULift.down h }
  fac s k := by
    ext n z
    apply ULift.ext
    rfl
  uniq s m hm := by
    ext n z
    apply NatTrans.ext
    funext k
    have h := congr_hom (congr_app (hm (Opposite.op k)) n) z
    exact congrArg ULift.down h

lemma hasLimit : HasLimit (lifted K A Y) := ⟨⟨cone K A Y, coneIsLimit K A Y⟩⟩

/-- Comparison to any chosen ordinary limit of the lifted pointwise Hom. -/
def iso [HasLimit (lifted K A Y)] : diagramHom K A Y ≅ limit (lifted K A Y) :=
  (coneIsLimit K A Y).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc]
lemma iso_hom_π [HasLimit (lifted K A Y)] (k : Kᵒᵖ) :
    (iso K A Y).hom ≫ limit.π (lifted K A Y) k = (cone K A Y).π.app k :=
  (limit.isLimit _).fac _ k

variable {Y}

def mapTarget {Z : C} (f : Y ⟶ Z) : lifted K A Y ⟶ lifted K A Z :=
  Functor.whiskerRight (Functor.whiskerLeft A.flip.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor.flip.map f))
    SSet.uliftFunctor.{w,v}

@[reassoc]
lemma iso_target_naturality {Z : C} (f : Y ⟶ Z)
    [HasLimit (lifted K A Y)] [HasLimit (lifted K A Z)] :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map ((Functor.const K).map f) ≫ (iso K A Z).hom =
      (iso K A Y).hom ≫ lim.map (mapTarget K A f) := by
  apply limit.hom_ext
  intro k
  rw [Category.assoc, iso_hom_π, Category.assoc, limit.map_π,
    ← Category.assoc, iso_hom_π]
  ext n a
  rfl

variable {A}

def mapSource {B : SimplexCategory ⥤ K ⥤ C} (a : A ⟶ B) : lifted K B Y ⟶ lifted K A Y :=
  Functor.whiskerRight (Functor.whiskerRight
    (NatTrans.op ((flipFunctor SimplexCategory K C).map a))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor.flip.obj Y)) SSet.uliftFunctor.{w,v}

@[reassoc]
lemma iso_source_naturality {B : SimplexCategory ⥤ K ⥤ C} (a : A ⟶ B)
    [HasLimit (lifted K A Y)] [HasLimit (lifted K B Y)] :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a).app ((Functor.const K).obj Y) ≫ (iso K A Y).hom =
      (iso K B Y).hom ≫ lim.map (mapSource K (Y := Y) a) := by
  apply limit.hom_ext
  intro k
  rw [Category.assoc, iso_hom_π, Category.assoc, limit.map_π,
    ← Category.assoc, iso_hom_π]
  ext n b
  rfl

end SerrePositivity.DiagramModel.MappingLimit
