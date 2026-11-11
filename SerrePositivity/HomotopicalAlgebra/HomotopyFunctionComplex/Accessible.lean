module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHom
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleColimits
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleFactorization
public import SerrePositivity.HomotopicalAlgebra.Smith.Smallness

/-! # Accessibility of actual resolution Hom at fixed sources

All degrees of a small family of cosimplicial objects admit a common
presentability cardinal. Composing their actual Hom with an accessible
target replacement gives accessible SSet-valued functors. This does not
assert a uniform cardinal for all source objects of a large category.
-/

@[expose] public section
universe w t v u vS
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C]

lemma cosimplicialHom_isCardinalAccessible (A : SimplexCategory ⥤ C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ n, IsCardinalPresentable (A.obj n) κ] :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).IsCardinalAccessible κ := by
  have : ∀ n, Functor.IsCardinalAccessible
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A ⋙ (evaluation SimplexCategoryᵒᵖ (Type v)).obj n) κ := fun n ↦
    inferInstanceAs ((coyoneda.obj (op (A.obj n.unop))).IsCardinalAccessible κ)
  exact Smith.AccessibleColimits.functorCategory_isCardinalAccessible _ κ

lemma resolutionHom_isCardinalAccessible (Q : C ⥤ (SimplexCategory ⥤ C)) (R : C ⥤ C)
    (X : Cᵒᵖ) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [R.IsCardinalAccessible κ] [∀ n, IsCardinalPresentable ((Q.obj X.unop).obj n) κ] :
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom Q R).obj X).IsCardinalAccessible κ := by
  have := cosimplicialHom_isCardinalAccessible (Q.obj X.unop) κ
  exact inferInstanceAs ((R ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (Q.obj X.unop)).IsCardinalAccessible κ)

/-- One cardinal bounds every degree of the entire fixed small family. -/
lemma exists_common_degree_presentability [IsAccessibleCategory.{w} C]
    {ι : Type t} [Small.{w} ι] (A : ι → SimplexCategory ⥤ C) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∀ i n, IsCardinalPresentable ((A i).obj n) κ := by
  obtain ⟨κ, hκ, h⟩ := Smith.exists_common_presentability
    (fun x : ι × SimplexCategory ↦ (A x.1).obj x.2)
  exact ⟨κ, hκ, fun i n ↦ h (i, n)⟩

lemma exists_accessible_resolutionHom_family [IsAccessibleCategory.{w} C]
    {ι : Type t} [Small.{w} ι] (Q : C ⥤ (SimplexCategory ⥤ C)) (R : C ⥤ C)
    [R.IsAccessible.{w}] (a : ι → C) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      R.IsCardinalAccessible κ ∧
      (∀ i n, IsCardinalPresentable ((Q.obj (a i)).obj n) κ) ∧
      (∀ i, ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom Q R).obj (op (a i))).IsCardinalAccessible κ) := by
  obtain ⟨κ₀, h₀, hR⟩ := Functor.IsAccessible.exists_cardinal R
  obtain ⟨μ, hμ, hA⟩ := exists_common_degree_presentability (fun i ↦ Q.obj (a i))
  obtain ⟨κ, hκ, h₀κ, hμκ⟩ := Cardinal.SharplyLT.exists_of_pair κ₀ μ
  have hR' := R.isCardinalAccessible_of_le h₀κ.le
  have hA' : ∀ i n, IsCardinalPresentable ((Q.obj (a i)).obj n) κ := by
    intro i n
    have := hA i n
    exact isCardinalPresentable_of_le _ hμκ.le
  refine ⟨κ, hκ, hR', hA', fun i ↦ ?_⟩
  have := hA' i
  exact resolutionHom_isCardinalAccessible Q R (op (a i)) κ

namespace MappingTests

/-- Precomposition with the actual source map, retaining the target variable. -/
def arrow (F : Cᵒᵖ ⥤ C ⥤ SSet.{vS}) (f : Arrow C) : C ⥤ Arrow SSet.{vS} where
  obj Y := Arrow.mk ((F.map f.hom.op).app Y)
  map g := Arrow.homMk ((F.obj (op f.right)).map g) ((F.obj (op f.left)).map g)
    ((F.map f.hom.op).naturality g)
  map_id Y := by ext <;> simp
  map_comp g h := by ext <;> simp

/-- All tests in a fixed family, as a single functor. -/
abbrev family {ι : Type t} (F : Cᵒᵖ ⥤ C ⥤ SSet.{vS}) (s : ι → Arrow C) :
    C ⥤ Discrete ι ⥤ Arrow SSet.{vS} :=
  (Discrete.functor (fun i ↦ arrow F (s i))).flip

lemma arrow_isCardinalAccessible (F : Cᵒᵖ ⥤ C ⥤ SSet.{vS}) (f : Arrow C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [(F.obj (op f.left)).IsCardinalAccessible κ]
    [(F.obj (op f.right)).IsCardinalAccessible κ] :
    (arrow F f).IsCardinalAccessible κ := by
  have : (arrow F f ⋙ Arrow.leftFunc).IsCardinalAccessible κ :=
    inferInstanceAs ((F.obj (op f.right)).IsCardinalAccessible κ)
  have : (arrow F f ⋙ Arrow.rightFunc).IsCardinalAccessible κ :=
    inferInstanceAs ((F.obj (op f.left)).IsCardinalAccessible κ)
  exact Smith.AccessibleFactorization.arrowFunctor_isCardinalAccessible _ κ

lemma family_isCardinalAccessible {ι : Type t} (F : Cᵒᵖ ⥤ C ⥤ SSet.{vS}) (s : ι → Arrow C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ i, (F.obj (op (s i).left)).IsCardinalAccessible κ]
    [∀ i, (F.obj (op (s i).right)).IsCardinalAccessible κ] :
    (family F s).IsCardinalAccessible κ := by
  have : ∀ i, Functor.IsCardinalAccessible
      (family F s ⋙ (evaluation (Discrete ι) (Arrow SSet.{vS})).obj i) κ :=
    fun ⟨i⟩ ↦ arrow_isCardinalAccessible F (s i) κ
  exact Smith.AccessibleColimits.functorCategory_isCardinalAccessible _ κ

end MappingTests
end SerrePositivity.HomotopyFunctionComplex
