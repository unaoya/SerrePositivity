module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CosimplicialMapFamily

/-! # Two-sided parameterized composition on the actual mixed diagonal Hom

The target diagram is written cosimplicially in the opposite category.
Both action orders are equal as actual simplicial maps, by associativity.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite

namespace SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom
variable {C : Type u} [Category.{v} C]

def obj (A : SimplexCategory ⥤ C) (B : SimplexCategory ⥤ Cᵒᵖ) : SSet.{v} where
  obj n := A.obj n.unop ⟶ (B.obj n.unop).unop
  map θ := ↾fun h => A.map θ.unop ≫ h ≫ (B.map θ.unop).unop
  map_id n := by
    ext h
    change A.map (𝟙 n.unop) ≫ h ≫ (B.map (𝟙 n.unop)).unop = h
    rw [A.map_id, B.map_id, unop_id, Category.id_comp, Category.comp_id]
  map_comp θ σ := by
    ext h
    change A.map (σ.unop ≫ θ.unop) ≫ h ≫ (B.map (σ.unop ≫ θ.unop)).unop =
      A.map σ.unop ≫ (A.map θ.unop ≫ h ≫ (B.map θ.unop).unop) ≫ (B.map σ.unop).unop
    simp only [Functor.map_comp, unop_comp, Category.assoc]

variable {T U : SSet.{v}} {A D : SimplexCategory ⥤ C} {B E : SimplexCategory ⥤ Cᵒᵖ}

def action (a : CosimplicialMapFamily T D A) (b : CosimplicialMapFamily T E B)
    (t : T ⟶ obj A B) : T ⟶ obj D E where
  app n := ↾fun x => a.app n x ≫ t.app n x ≫ (b.app n x).unop
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    have ht := congrArg (fun k => k x) (t.naturality θ)
    change t.app m (T.map θ x) = A.map θ.unop ≫ t.app n x ≫ (B.map θ.unop).unop at ht
    have hb := congrArg Quiver.Hom.unop (b.naturality θ x)
    change (b.app n x).unop ≫ (E.map θ.unop).unop =
      (B.map θ.unop).unop ≫ (b.app m (T.map θ x)).unop at hb
    change a.app m (T.map θ x) ≫ t.app m (T.map θ x) ≫
        (b.app m (T.map θ x)).unop =
      D.map θ.unop ≫ (a.app n x ≫ t.app n x ≫ (b.app n x).unop) ≫ (E.map θ.unop).unop
    rw [ht]
    calc
      _ = (a.app m (T.map θ x) ≫ A.map θ.unop) ≫ t.app n x ≫
          ((B.map θ.unop).unop ≫ (b.app m (T.map θ x)).unop) := by
        simp only [Category.assoc]
      _ = (D.map θ.unop ≫ a.app n x) ≫ t.app n x ≫
          ((b.app n x).unop ≫ (E.map θ.unop).unop) := by rw [← a.naturality, ← hb]
      _ = _ := by simp only [Category.assoc]

@[simp] lemma action_app (a : CosimplicialMapFamily T D A) (b : CosimplicialMapFamily T E B)
    (t : T ⟶ obj A B) (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    (action a b t).app n x = a.app n x ≫ t.app n x ≫ (b.app n x).unop := rfl

def pre (a : CosimplicialMapFamily T D A) (t : T ⟶ obj A B) : T ⟶ obj D B :=
  action a (CosimplicialMapFamily.identity B) t

def post (b : CosimplicialMapFamily T E B) (t : T ⟶ obj A B) : T ⟶ obj A E :=
  action (CosimplicialMapFamily.identity A) b t

@[simp] lemma pre_app (a : CosimplicialMapFamily T D A) (t : T ⟶ obj A B)
    (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    (pre a t).app n x = a.app n x ≫ t.app n x := by
  change a.app n x ≫ t.app n x ≫ (𝟙 _).unop = _
  exact congrArg (fun k => a.app n x ≫ k) (Category.comp_id (t.app n x))

@[simp] lemma post_app (b : CosimplicialMapFamily T E B) (t : T ⟶ obj A B)
    (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    (post b t).app n x = t.app n x ≫ (b.app n x).unop := by
  change 𝟙 _ ≫ (t.app n x ≫ (b.app n x).unop) = _
  exact Category.id_comp _

lemma action_eq_post_pre (a : CosimplicialMapFamily T D A)
    (b : CosimplicialMapFamily T E B) (t : T ⟶ obj A B) :
    action a b t = post b (pre a t) := by
  ext n x
  dsimp [action, pre, post, CosimplicialMapFamily.identity, CosimplicialMapFamily.ofMap]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]

lemma pre_post (a : CosimplicialMapFamily T D A) (b : CosimplicialMapFamily T E B)
    (t : T ⟶ obj A B) : pre a (post b t) = post b (pre a t) := by
  ext n x
  dsimp [pre, post, action, CosimplicialMapFamily.identity, CosimplicialMapFamily.ofMap]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]

@[reassoc]
lemma action_parameter (a : CosimplicialMapFamily T D A) (b : CosimplicialMapFamily T E B)
    (t : T ⟶ obj A B) (f : U ⟶ T) :
    f ≫ action a b t = action (a.reindex f) (b.reindex f) (f ≫ t) := by
  ext n x
  rfl

def map (a : D ⟶ A) (b : E ⟶ B) : obj A B ⟶ obj D E :=
  action (CosimplicialMapFamily.ofMap a) (CosimplicialMapFamily.ofMap b) (𝟙 (obj A B))

@[simp] lemma map_app (a : D ⟶ A) (b : E ⟶ B) (n : SimplexCategoryᵒᵖ)
    (h : A.obj n.unop ⟶ (B.obj n.unop).unop) :
    (map a b).app n h = a.app n.unop ≫ h ≫ (b.app n.unop).unop := rfl

end SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom
