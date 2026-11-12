module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedFamily

/-!
概要：再構成した全族の二短辺は、元の二つの標準 coherent 区間族を厳密に回収する。
方針：短辺のラベルには変更対象の長 Hom がなく、既存の合成三角形へ戻る。
規約：K・L の全パラメーターを保持する。
使われ方：元の全ホーン a の厳密保持。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C}
  {K L : SSet.{max u v}}
  (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
  (g : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z))
  (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z))
  (hM : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 ((K ⊗ K) ⊗ L) ≫ M =
    lift (fst (K ⊗ K) L ≫ fst K K ≫ f)
      (fst (K ⊗ K) L ≫ snd K K ≫ g) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, v}
      (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
      (SSet.uliftFunctor.{v, u}).map (eComp SSet X Y Z))

lemma triangleSeparatedFamily_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ L)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedFamily f g M hM =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (fst K L ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y) := by
  calc
    _ = (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ L)) ≫
        (Δ[2] ◁ lift (fst K L ≫ f) (fst K L ≫ g)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionTriangle X Y Z := by
      apply SSet.hom_ext
      rintro ⟨⟨n⟩⟩
      apply ConcreteCategory.hom_ext
      rintro ⟨t, s, r⟩
      let l := (stdSimplex.objEquiv ((stdSimplex.δ (2 : Fin 3)).app
        (Opposite.op ⦋n⦌) t)).toOrderHom
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex f g M hM s r l = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex_eq_baseline_of_no_long f g M hM s r l (by
        intro i j
        right
        have h : ∀ k : Fin 2, (SimplexCategory.δ (2 : Fin 3)).toOrderHom k ≠ 2 := by decide
        exact h ((stdSimplex.objEquiv t).toOrderHom j))]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelBaseline_realization (f.app (Opposite.op ⦋n⦌) s).down
        (g.app (Opposite.op ⦋n⦌) s).down l).symm
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionTriangle_first_precomp]
      rfl

lemma triangleSeparatedFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ L)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedFamily f g M hM =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (fst K L ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison Y Z) := by
  calc
    _ = (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ L)) ≫
        (Δ[2] ◁ lift (fst K L ≫ f) (fst K L ≫ g)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionTriangle X Y Z := by
      apply SSet.hom_ext
      rintro ⟨⟨n⟩⟩
      apply ConcreteCategory.hom_ext
      rintro ⟨t, s, r⟩
      let l := (stdSimplex.objEquiv ((stdSimplex.δ (0 : Fin 3)).app
        (Opposite.op ⦋n⦌) t)).toOrderHom
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex f g M hM s r l = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex_eq_baseline_of_no_long f g M hM s r l (by
        intro i j
        left
        have h : ∀ k : Fin 2, (SimplexCategory.δ (0 : Fin 3)).toOrderHom k ≠ 0 := by decide
        exact h ((stdSimplex.objEquiv t).toOrderHom i))]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelBaseline_realization (f.app (Opposite.op ⦋n⦌) s).down
        (g.app (Opposite.op ⦋n⦌) s).down l).symm
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionTriangle_last_precomp]
      rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
