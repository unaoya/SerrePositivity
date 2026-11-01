module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.EnrichedDegreeCategory

/-!
# 元の豊穣目標の全単体作用素の対象恒等の関手

概要：元の Hom の単体作用を各次数の評価圏の間の関手にする。
方針：元の単位・合成の単体的自然性を同じ点で評価する。
規約：対象の選択を変更せず、全単体作用素を使う。
使われ方：自由積の普遍的な評価の単体的自然性。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.EnrichedDegree
open CategoryTheory

variable {D : Type uD} [EnrichedCategory SSet.{u} D] {n m k : SimplexCategoryᵒᵖ}

def simplexFunctor (θ : n ⟶ m) :
    @CategoryTheory.Functor (Objects D) (category n) (Objects D) (category m) :=
  @CategoryTheory.Functor.mk (Objects D) (category n) (Objects D) (category m)
    (fun X => X) (fun {X Y} p => (X ⟶[SSet.{u}] Y).map θ p)
    (fun X => (congrArg (fun f => f PUnit.unit) ((eId SSet.{u} X).naturality θ)).symm)
    (fun {X Y Z} p q =>
      (congrArg (fun f => f (p, q)) ((eComp SSet.{u} X Y Z).naturality θ)).symm)

lemma simplexFunctor_id : simplexFunctor (D := D) (𝟙 n) =
    @CategoryTheory.Functor.id (Objects D) (category n) := by
  refine @CategoryTheory.Functor.hext (Objects D) (category n) (Objects D) (category n)
    (simplexFunctor (D := D) (𝟙 n)) (@CategoryTheory.Functor.id (Objects D) (category n))
    (fun _ => rfl) ?_
  intro X Y p
  exact heq_of_eq (congrArg (fun f => f p) ((X ⟶[SSet.{u}] Y).map_id n))

lemma simplexFunctor_comp (θ : n ⟶ m) (φ : m ⟶ k) :
    simplexFunctor (D := D) (θ ≫ φ) =
      @CategoryTheory.Functor.comp (Objects D) (category n) (Objects D) (category m)
        (Objects D) (category k) (simplexFunctor θ) (simplexFunctor φ) := by
  refine @CategoryTheory.Functor.hext (Objects D) (category n) (Objects D) (category k)
    (simplexFunctor (D := D) (θ ≫ φ))
    (@CategoryTheory.Functor.comp (Objects D) (category n) (Objects D) (category m)
      (Objects D) (category k) (simplexFunctor θ) (simplexFunctor φ)) (fun _ => rfl) ?_
  intro X Y p
  exact heq_of_eq (congrArg (fun f => f p) ((X ⟶[SSet.{u}] Y).map_comp θ φ))

end SerrePositivity.EInfinity.Hammock.EnrichedDegree
