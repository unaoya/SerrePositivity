module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedMiddleHom

/-!
概要：内部合成の全座標の等式を、元の小さい豊穣圏の合成則として公開する。
方針：二短辺の作用を元の宇宙へ戻し、ulift の直積同型で合成を照合する。
規約：豊穣合成は元の eComp を使う。
使われ方：全族の制御二胞体を豊穣関手として組み立てる。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

lemma triangleSeparatedLongHom_comp_middle_enriched
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C}
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
    {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    {i j k : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
        ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom M s r t hi k =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedHom
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) j) s f ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel t)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel_zero_of_ne t (i := j) (by omega)) k) s g) ≫
        eComp SSet X Y Z := by
  apply (SSet.uliftFunctor.{v, u}).map_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom_comp_middle f g _ M hM s r t hi hj, Functor.map_comp]
  erw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedHom_map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) j) s f,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedHom_map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel t)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel_zero_of_ne t (i := j) (by omega)) k) s g]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨P, Q⟩⟩
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
