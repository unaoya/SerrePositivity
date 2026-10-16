module

public import SerrePositivity.CategoryTheory.Quiver.PathNatTrans
public import SerrePositivity.HomotopicalAlgebra.Simplicial.WordPresentationRealization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.WordPresentationDiagram

/-! # Evaluation of every presented word arrow commutes with every simplex map -/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.WordPresentationNaturality
open WordPresentationRealization
variable {C : Type u} [Category.{w} C] {T : SSet.{v}}
  (F : C ⥤ ParameterCategory.Object T) (K : C → SSet.{v})
  (s : ∀ X, K X ⟶ (F.obj X).value) (p : ∀ X, (F.obj X).value ⟶ K X)
  (hs : ∀ X, s X ≫ p X = 𝟙 (K X))
  (H : ∀ X, SSet.Homotopy (𝟙 (F.obj X).value) (p X ≫ s X))
  (hP : ∀ X, (H X).h ≫ p X = fst (F.obj X).value WordSegment.interval ≫ p X)
  (hS : ∀ X, s X ▷ WordSegment.interval ≫ (H X).h = fst (K X) WordSegment.interval ≫ s X)

abbrev R (n : SimplexCategoryᵒᵖ) (t : T.obj n) := realization F K s p hs H hP hS n t

variable {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (t : T.obj n)

abbrev target := RetractWords.quotient C (WordSegment.degree.{v} n) ⋙
  RetractWords.map (𝟭 C) (WordSegment.degreeMap θ) ⋙
    (R F K s p hs H hP hS m (T.map θ t)).functor

def component : ∀ X : RetractWords.Raw C (WordSegment.degree.{v} n),
    (R F K s p hs H hP hS n t).raw.obj X ⟶ (target F K s p hs H hP hS θ t).obj X
  | .ambient X => (F.obj X).value.map θ
  | .small X => (K X).map θ

lemma edge_naturality {X Y : RetractWords.Vertex C (WordSegment.degree.{v} n)}
    (e : X ⟶ Y) :
    (R F K s p hs H hP hS n t).raw.map ((Paths.of _).map e) ≫
        component F K s p hs H hP hS θ t Y =
      component F K s p hs H hP hS θ t X ≫
        (target F K s p hs H hP hS θ t).map ((Paths.of _).map e) := by
  cases e with
  | source f =>
    apply ConcreteCategory.hom_ext
    intro x
    change (F.obj _).value.map θ ((F.map f).app n (x, t)) =
      (F.map f).app m ((F.obj _).value.map θ x, T.map θ t)
    exact (types_congr_hom ((F.map f).naturality θ) (x, t)).symm
  | word X w =>
    apply ConcreteCategory.hom_ext
    intro x
    change (F.obj X).value.map θ
      (WordRetractionAction.eval (s X) (p X) (hs X) (H X) (hP X) (hS X) n w x) =
      WordRetractionAction.eval (s X) (p X) (hs X) (H X) (hP X) (hS X) m (WordSegment.degreeMap θ w)
        ((F.obj X).value.map θ x)
    exact WordRetractionAction.eval_naturality (s X) (p X) (hs X) (H X) (hP X) (hS X) θ w x
  | section_ X =>
    apply ConcreteCategory.hom_ext
    intro x
    change (F.obj X).value.map θ ((s X).app n x) = (s X).app m ((K X).map θ x)
    exact (types_congr_hom ((s X).naturality θ) x).symm
  | projection X =>
    apply ConcreteCategory.hom_ext
    intro x
    change (K X).map θ ((p X).app n x) = (p X).app m ((F.obj X).value.map θ x)
    exact (types_congr_hom ((p X).naturality θ) x).symm

def rawNatTrans : (R F K s p hs H hP hS n t).raw ⟶ target F K s p hs H hP hS θ t :=
  QuiverPaths.natTransOfEdges _ _ (component F K s p hs H hP hS θ t)
    (edge_naturality F K s p hs H hP hS θ t)

def natTrans : (R F K s p hs H hP hS n t).functor ⟶
    RetractWords.map (𝟭 C) (WordSegment.degreeMap θ) ⋙
      (R F K s p hs H hP hS m (T.map θ t)).functor :=
  CategoryTheory.Quotient.natTransLift _ (rawNatTrans F K s p hs H hP hS θ t)

lemma small_naturality (X Y : C)
    (f : (WordPresentationDiagram.smallHom.{u, w, v} C X Y).obj n) (x : (K X).obj n) :
    (K Y).map θ ((R F K s p hs H hP hS n t).functor.map f x) =
      (R F K s p hs H hP hS m (T.map θ t)).functor.map
        ((WordPresentationDiagram.smallHom C X Y).map θ f) ((K X).map θ x) :=
  types_congr_hom ((natTrans F K s p hs H hP hS θ t).naturality f) x

end SerrePositivity.SimplicialModel.WordPresentationNaturality
