module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleSeparatedFamily
public import SerrePositivity.InfinityCategories.F1.Coherent.HomMono

/-!
概要：等しい再構成 coherent 単体から、置換した長 Hom 全体を取り出す。
方針：対象が補助パラメーターに依存しないことを使い、同じ Hom 表示へ戻す。
規約：直接 path の値だけでなく、native Hom の写像全体の等号。
使われ方：実 encoder の等号から区間・高次パラメーターを回収する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma triangleSeparatedSimplex_longHom_eq_of_eq
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C}
    {K L : SSet.{max u v}}
    (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z))
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z))
    (hM : prismEndpoint 1 ((K ⊗ K) ⊗ L) ≫ M =
      lift (fst (K ⊗ K) L ≫ fst K K ≫ f) (fst (K ⊗ K) L ≫ snd K K ≫ g) ≫
        (HomotopyLimits.uliftTensorIso.{u, v}
          (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
        (SSet.uliftFunctor.{v, u}).map (eComp SSet X Y Z))
    {n : ℕ} (s : K _⦋n⦌) (r r' : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    (h : triangleSeparatedSimplex f g M hM s r t = triangleSeparatedSimplex f g M hM s r' t)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 2) :
    triangleSeparatedLongHom M s r t hi j = triangleSeparatedLongHom M s r' t hi j := by
  have hm : triangleSeparatedAssignedHom f g M s r t i j =
      triangleSeparatedAssignedHom f g M s r' t i j :=
    eq_of_heq (enrichedFunctor_map_heq h ⟨ULift.up i⟩ ⟨ULift.up j⟩)
  have hn := congrArg (fun a => a ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
    (triangleSeparatedBaseline_obj_zero f g s t i hi)
    (triangleSeparatedBaseline_obj_two f g s t j hj))) hm
  rw [triangleSeparatedAssignedHom_long f g M s r t i j hi hj,
    triangleSeparatedAssignedHom_long f g M s r' t i j hi hj] at hn
  exact hn

end SerrePositivity.InfinityCategories
