module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedFamily
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomMono

/-!
概要：等しい再構成 coherent 単体から、置換した長 Hom 全体を取り出す。
方針：対象が補助パラメーターに依存しないことを使い、同じ Hom 表示へ戻す。
規約：直接 path の値だけでなく、native Hom の写像全体の等号。
使われ方：実 encoder の等号から区間・高次パラメーターを回収する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

lemma triangleSeparatedSimplex_longHom_eq_of_eq
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C}
    {K L : SSet.{max u v}}
    (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z))
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z))
    (hM : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 ((K ⊗ K) ⊗ L) ≫ M =
      lift (fst (K ⊗ K) L ≫ fst K K ≫ f) (fst (K ⊗ K) L ≫ snd K K ≫ g) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, v}
          (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
        (SSet.uliftFunctor.{v, u}).map (eComp SSet X Y Z))
    {n : ℕ} (s : K _⦋n⦌) (r r' : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex f g M hM s r t = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex f g M hM s r' t)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom M s r t hi j = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom M s r' t hi j := by
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom f g M s r t i j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom f g M s r' t i j :=
    eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctor_map_heq h ⟨ULift.up i⟩ ⟨ULift.up j⟩)
  have hn := congrArg (fun a => a ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_zero f g s t i hi)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_two f g s t j hj))) hm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom_long f g M s r t i j hi hj,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom_long f g M s r' t i j hi hj] at hn
  exact hn

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
