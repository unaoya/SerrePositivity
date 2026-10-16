module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiscreteFiber

/-! # Actual disjoint unions of simplicial sets with discrete labels

Maps into the total space can be extracted on each label fiber and
reassembled from entire fiber families, preserving the label exactly.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.DiscreteFamily
variable {I : Type v} (F : I → SSet.{v})

def total : SSet.{v} where
  obj n := Σ i, (F i).obj n
  map θ := ↾fun x => ⟨x.1, (F x.1).map θ x.2⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    exact congrArg (Sigma.mk i) (types_congr_hom ((F i).map_id n) x)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    exact congrArg (Sigma.mk i) (types_congr_hom ((F i).map_comp f g) x)

def projection : total F ⟶ PiZeroConstant.discrete I where
  app _ := ↾Sigma.fst
  naturality {_ _} _ := by apply ConcreteCategory.hom_ext; intro x; rfl

def inclusion (i : I) : F i ⟶ total F where
  app n := ↾fun x => (⟨i, x⟩ : (total F).obj n)
  naturality {_ _} _ := by apply ConcreteCategory.hom_ext; intro x; rfl

variable {X : SSet.{v}} (b : X ⟶ PiZeroConstant.discrete I)

def assembleFn (d : ∀ i, DiscreteFiber.obj b i ⟶ F i)
    (n : SimplexCategoryᵒᵖ) (x : X.obj n) : (total F).obj n :=
  ⟨b.app n x, (d (b.app n x)).app n ⟨x, rfl⟩⟩

lemma assembleFn_eq (d : ∀ i, DiscreteFiber.obj b i ⟶ F i)
    (n : SimplexCategoryᵒᵖ) (x : X.obj n) (i : I) (hi : b.app n x = i) :
    assembleFn F b d n x = ⟨i, (d i).app n ⟨x, hi⟩⟩ := by
  subst i
  rfl

def assemble (d : ∀ i, DiscreteFiber.obj b i ⟶ F i) : X ⟶ total F where
  app n := ↾assembleFn F b d n
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    change assembleFn F b d m (X.map θ x) =
      ⟨b.app n x, (F (b.app n x)).map θ ((d (b.app n x)).app n ⟨x, rfl⟩)⟩
    rw [assembleFn_eq F b d m _ (b.app n x) (DiscreteFiber.label_naturality b θ x)]
    exact congrArg (Sigma.mk (b.app n x))
      (types_congr_hom ((d (b.app n x)).naturality θ) ⟨x, rfl⟩)

lemma assemble_projection (d : ∀ i, DiscreteFiber.obj b i ⟶ F i) :
    assemble F b d ≫ projection F = b := rfl

def extractFn (a : X ⟶ total F) (ha : a ≫ projection F = b) (i : I)
    (n : SimplexCategoryᵒᵖ) (x : (DiscreteFiber.obj b i).obj n) : (F i).obj n :=
  Eq.rec (motive := fun k _ => (F k).obj n) (a.app n x.1).2
    ((types_congr_hom (congr_app ha n) x.1).trans x.2)

lemma mk_transport {i j : I} (h : i = j) (n : SimplexCategoryᵒᵖ) (x : (F i).obj n) :
    (⟨j, Eq.rec (motive := fun k _ => (F k).obj n) x h⟩ : (total F).obj n) = ⟨i, x⟩ := by
  subst j
  rfl

lemma extractFn_spec (a : X ⟶ total F) (ha : a ≫ projection F = b) (i : I)
    (n : SimplexCategoryᵒᵖ) (x : (DiscreteFiber.obj b i).obj n) :
    (⟨i, extractFn F b a ha i n x⟩ : (total F).obj n) = a.app n x.1 := by
  exact mk_transport F _ n _

def extract (a : X ⟶ total F) (ha : a ≫ projection F = b) (i : I) :
    DiscreteFiber.obj b i ⟶ F i where
  app n := ↾extractFn F b a ha i n
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply sigma_mk_injective (i := i)
    change (⟨i, extractFn F b a ha i m ((DiscreteFiber.obj b i).map θ x)⟩ :
      (total F).obj m) = ⟨i, (F i).map θ (extractFn F b a ha i n x)⟩
    rw [extractFn_spec]
    change a.app m (X.map θ x.1) = ⟨i, (F i).map θ (extractFn F b a ha i n x)⟩
    have hn := types_congr_hom (a.naturality θ) x.1
    change a.app m (X.map θ x.1) = (total F).map θ (a.app n x.1) at hn
    rw [hn, ← extractFn_spec F b a ha i n x]
    rfl

lemma assemble_extract (a : X ⟶ total F) (ha : a ≫ projection F = b) :
    assemble F b (extract F b a ha) = a := by
  ext n x
  exact extractFn_spec F b a ha (b.app n x) n ⟨x, rfl⟩

def fiberInclusion (i : I) : F i ⟶ DiscreteFiber.obj (projection F) i where
  app _ := ↾fun x => ⟨⟨i, x⟩, rfl⟩
  naturality {_ _} _ := by apply ConcreteCategory.hom_ext; intro x; rfl

def fiberIso (i : I) : DiscreteFiber.obj (projection F) i ≅ F i where
  hom := extract F (projection F) (𝟙 _) (Category.id_comp _) i
  inv := fiberInclusion F i
  hom_inv_id := by
    ext n x
    apply Subtype.ext
    exact extractFn_spec F (projection F) (𝟙 _) (Category.id_comp _) i n x
  inv_hom_id := by ext n x; rfl

end SerrePositivity.SimplicialModel.DiscreteFamily
