module

public import Mathlib.AlgebraicTopology.SimplicialSet.NerveCodiscrete
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

/-! # Vertex functions extend uniquely to maps into a codiscrete nerve

For an inhabited label type this nerve is injective against all simplicial
monomorphisms, and in particular Kan, in any value universe without a model.
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.SimplicialModel.CodiscreteNerveExtension
variable {I : Type u} {X : SSet.{u}}

abbrev zero : SimplexCategoryᵒᵖ := op (SimplexCategory.mk 0)

abbrev vertex (n : SimplexCategoryᵒᵖ) (j : Fin (n.unop.len + 1)) : n ⟶ zero :=
  (SimplexCategory.const (SimplexCategory.mk 0) n.unop j).op

def fromVertices (v : X.obj zero → I) : X ⟶ nerve (Codiscrete I) where
  app n := ↾fun x => Codiscrete.functor (fun j => v (X.map (vertex n j) x))
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Codiscrete.equivFun.injective
    funext j
    exact congrArg v ((types_congr_hom (X.map_comp θ (vertex m j)) x).symm)

def vertices (f : X ⟶ nerve (Codiscrete I)) : X.obj zero → I :=
  fun x => ((f.app zero x).obj 0).as

lemma vertices_fromVertices (v : X.obj zero → I) : vertices (fromVertices v) = v := by
  funext x
  change v (X.map (vertex zero 0) x) = v x
  have he : vertex zero 0 = 𝟙 zero := by
    apply Quiver.Hom.unop_inj
    ext j
    change (0 : ℕ) = j.val
    have hj : j.val < 1 := j.isLt
    omega
  rw [he, X.map_id]
  rfl

lemma fromVertices_vertices (f : X ⟶ nerve (Codiscrete I)) :
    fromVertices (vertices f) = f := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Codiscrete.equivFun.injective
  funext j
  exact congrArg (fun c => (c.obj 0).as)
    (types_congr_hom (f.naturality (vertex n j)) x)

def homEquiv : (X ⟶ nerve (Codiscrete I)) ≃ (X.obj zero → I) where
  toFun := vertices
  invFun := fromVertices
  left_inv := fromVertices_vertices
  right_inv := vertices_fromVertices

lemma exists_extension {A B : SSet.{u}} (j : A ⟶ B) [Mono j]
    (f : A ⟶ nerve (Codiscrete I)) (i : I) :
    ∃ g : B ⟶ nerve (Codiscrete I), j ≫ g = f := by
  have hj : Function.Injective (j.app zero) :=
    (mono_iff_injective _).mp inferInstance
  let v : B.obj zero → I := Function.extend (j.app zero) (vertices f) (fun _ => i)
  refine ⟨fromVertices v, homEquiv.injective ?_⟩
  funext x
  change vertices (fromVertices v) (j.app zero x) = vertices f x
  rw [vertices_fromVertices]
  exact hj.extend_apply _ _ _

lemma terminal_mono_rlp (i : I) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (terminal.from (nerve (Codiscrete I))) := by
  intro A B j hj
  have : Mono j := hj
  refine ⟨fun {f g} _ => ?_⟩
  obtain ⟨l, hl⟩ := exists_extension j f i
  exact ⟨⟨{ l := l, fac_left := hl, fac_right := terminal.hom_ext _ _ }⟩⟩

lemma terminal_horn_rlp (i : I) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (nerve (Codiscrete I))) := by
  intro A B j hj
  exact terminal_mono_rlp i j (SSet.modelCategoryQuillen.J_le_monomorphisms j hj)

lemma kanComplex (i : I) : SSet.KanComplex (nerve (Codiscrete I)) :=
  (SSet.modelCategoryQuillen.fibration_iff _).mpr (terminal_horn_rlp i)

end SerrePositivity.SimplicialModel.CodiscreteNerveExtension
