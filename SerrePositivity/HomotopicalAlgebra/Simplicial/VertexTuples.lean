module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Simplicial ordered tuples and their prescribed vertices

An n-simplex is an ordered list of n+1 vertices. Face and degeneracy maps
delete and repeat entries. The constant simplicial set of vertices embeds
monomorphically, allowing simultaneous extensions with all simplicial
identities, instead of unrelated choices in each dimension.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.VertexTuples

def obj (A : Type v) : SSet.{v} where
  obj n := Fin (n.unop.len + 1) → A
  map θ := ↾fun a i => a (θ.unop.toOrderHom i)

abbrev vertices (A : Type v) : SSet.{v} := (Functor.const SimplexCategoryᵒᵖ).obj A

def inclusion (A : Type v) : vertices A ⟶ obj A where
  app _ := ↾fun a _ => a

instance (A : Type v) : Mono (inclusion A) := by
  have : ∀ n, Mono ((inclusion A).app n) := fun n =>
    (CategoryTheory.mono_iff_injective _).mpr (fun a b h => congrFun h 0)
  exact NatTrans.mono_of_mono_app _

def vertex {A : Type v} (a : A) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ vertices A where
  app _ := ↾fun _ => a

/-- An explicit simplex, with its full ordered tuple of vertices. -/
def simplex {A : Type v} {n : ℕ} (a : Fin (n + 1) → A) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ obj A where
  app _ := ↾fun x i => a ((SSet.stdSimplex.objEquiv x).toOrderHom i)

/-- All faces and degeneracies are computed by the same formula. -/
lemma simplex_naturality {A : Type v} {n m : ℕ}
    (a : Fin (n + 1) → A) (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ simplex a = simplex (fun i => a (θ.toOrderHom i)) := rfl

lemma vertex_inclusion {A : Type v} (a : A) :
    vertex a ≫ inclusion A = simplex (fun _ : Fin 1 => a) := rfl

/-- Assemble a specified point at each vertex, without choosing higher simplices. -/
def pointsMap {A : Type v} {K : SSet.{v}}
    (p : A → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ K)) : vertices A ⟶ K where
  app n := ↾fun a => (p a).app n (SSet.stdSimplex.const 0 0 n)
  naturality {n m} θ := by
    ext a
    exact congrArg (fun k => k (SSet.stdSimplex.const 0 0 n)) ((p a).naturality θ)

@[reassoc]
lemma vertex_pointsMap {A : Type v} {K : SSet.{v}}
    (p : A → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ K)) (a : A) :
    vertex a ≫ pointsMap p = p a := by
  ext n x
  change (p a).app n (SSet.stdSimplex.const 0 0 n) = (p a).app n x
  congr 1
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

end SerrePositivity.SimplicialModel.VertexTuples
