module

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleColimits
public import SerrePositivity.HomotopicalAlgebra.Smith.DependentCopower
public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.SmallObject.Construction

/-! # Accessible families of commutative squares

Each component is a representable on the arrow category. The resulting
dependent coproducts are the source and target coproducts of a cell-attachment
step, before taking its pushout.
-/

@[expose] public section
universe w u t
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.Smith.AccessibleSquares
variable {C : Type u} [Category.{w} C] {ι : Type t} [Small.{w} ι] (a : ι → Arrow C)

abbrev squareFamily : Arrow C ⥤ Discrete ι ⥤ Type w :=
  (Discrete.functor (fun i ↦ coyoneda.obj (op (a i)))).flip

/-- This is the actual square index used by the existing small-object construction. -/
abbrev indexEquiv (f : Arrow C) : DependentCopower.index ((squareFamily a).obj f) ≃
    SmallObject.FunctorObjIndex (fun i ↦ (a i).hom) f.hom where
  toFun x := ⟨x.1, x.2.left, x.2.right, x.2.w⟩
  invFun x := ⟨x.i, Arrow.homMk x.t x.b x.w⟩
  left_inv _x := rfl
  right_inv _x := rfl

omit [Small.{w} ι] in
lemma squareFamily_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ i, IsCardinalPresentable (a i) κ] : (squareFamily a).IsCardinalAccessible κ := by
  have : ∀ i, (squareFamily a ⋙ (evaluation (Discrete ι) (Type w)).obj i).IsCardinalAccessible κ :=
    fun ⟨i⟩ ↦ inferInstanceAs ((coyoneda.obj (op (a i))).IsCardinalAccessible κ)
  exact AccessibleColimits.functorCategory_isCardinalAccessible _ κ

variable [HasColimitsOfSize.{w, w} C]

lemma hasSquareCoproducts {X Y : C} (f : X ⟶ Y) :
    HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex
      (fun i ↦ (a i).hom) f)) C :=
  hasCoproductsOfShape_of_small.{w} C _

attribute [local instance] hasSquareCoproducts DependentCopower.hasIndexCoproducts

lemma arrow_isCardinalPresentable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (f : Arrow C) [IsCardinalPresentable f.left κ] [IsCardinalPresentable f.right κ] :
    IsCardinalPresentable f κ :=
  Comma.isCardinalPresentable_mk (F₁ := 𝟭 C) (F₂ := 𝟭 C) f.hom

omit [Small.{w} ι] in
lemma squareFamily_isCardinalAccessible_of_endpoints (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ i, IsCardinalPresentable (a i).left κ]
    [∀ i, IsCardinalPresentable (a i).right κ] :
    (squareFamily a).IsCardinalAccessible κ := by
  have : ∀ i, IsCardinalPresentable (a i) κ := fun i ↦ arrow_isCardinalPresentable κ (a i)
  exact squareFamily_isCardinalAccessible a κ

abbrev cells (A : ι → C) : Arrow C ⥤ C := squareFamily a ⋙ DependentCopower.realization A

lemma cells_isCardinalAccessible (A : ι → C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ i, IsCardinalPresentable (a i).left κ]
    [∀ i, IsCardinalPresentable (a i).right κ] : (cells a A).IsCardinalAccessible κ := by
  have := squareFamily_isCardinalAccessible_of_endpoints a κ
  have := DependentCopower.realization_isCardinalAccessible A κ
  exact inferInstanceAs
    ((squareFamily a ⋙ DependentCopower.realization A).IsCardinalAccessible κ)

abbrev indexMap {f g : Arrow C} (φ : f ⟶ g)
    (x : SmallObject.FunctorObjIndex (fun i ↦ (a i).hom) f.hom) :
    SmallObject.FunctorObjIndex (fun i ↦ (a i).hom) g.hom :=
  ⟨x.i, x.t ≫ φ.left, x.b ≫ φ.right, by
    rw [Category.assoc, φ.w, ← Category.assoc, x.w, Category.assoc]⟩

/-- The dependent coproduct with precisely Mathlib's square index. -/
abbrev rawCells (A : ι → C) : Arrow C ⥤ C where
  obj f := ∐ (fun x : SmallObject.FunctorObjIndex (fun i ↦ (a i).hom) f.hom ↦ A x.i)
  map φ := Limits.Sigma.map' (indexMap a φ) (fun _ ↦ 𝟙 _)
  map_id f := by
    apply Sigma.hom_ext
    intro x
    simp [indexMap]
    congr 1
    cases x
    simp
  map_comp φ ψ := by
    apply Sigma.hom_ext
    intro x
    simp [indexMap]
    congr 1; simp [Category.assoc]

def cellsIsoRaw (A : ι → C) : cells a A ≅ rawCells a A :=
  NatIso.ofComponents
    (fun f ↦ Sigma.whiskerEquiv
      (f := fun x : DependentCopower.index ((squareFamily a).obj f) ↦ A x.1)
      (g := fun x : SmallObject.FunctorObjIndex (fun i ↦ (a i).hom) f.hom ↦ A x.i)
      (indexEquiv a f) (fun _ ↦ Iso.refl _)) (by
      intro f g φ
      apply Sigma.hom_ext
      intro x
      simp [cells, rawCells, DependentCopower.realization,
        Sigma.whiskerEquiv, indexEquiv, indexMap, squareFamily]
      rfl)

lemma rawCells_isCardinalAccessible (A : ι → C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ i, IsCardinalPresentable (a i).left κ]
    [∀ i, IsCardinalPresentable (a i).right κ] : (rawCells a A).IsCardinalAccessible κ := by
  have := cells_isCardinalAccessible a A κ
  exact Functor.isCardinalAccessible_of_natIso (cellsIsoRaw a A) κ

end SerrePositivity.Smith.AccessibleSquares
