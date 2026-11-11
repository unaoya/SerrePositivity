module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplexShapeFamilyColimit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexNervePushout

/-!
概要：単体圏の nerve は小さい余極限を全て保存する。
方針：各次数を射列の形で添字付けた評価関手の依存和と自然に同定する。
規約：底や図式の射に充填性・単射性を要求しない。
使われ方：小余積と transfinite なセル付加で反転関手を極限表示する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 底の単体集合を、その単体圏の実際の nerve へ送る関手。 -/
def transportSimplexNerveFunctor : SSet.{u} ⥤ SSet.{u} where
  obj B := nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)
  map f := nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor f)
  map_id B := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    change σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (𝟙 B) = σ
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor_id, Functor.comp_id]
  map_comp f g := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    change σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (f ≫ g) =
      (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor f) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor g
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor_comp, Functor.assoc]

/-- 一定次数の射列座標を与える、評価関手の依存和。 -/
def transportSimplexNerveDegreeFamily (n : ℕ) : SSet.{u} ⥤ Type u :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexShapeFamilyDiagram (fun τ : ComposableArrows SimplexCategoryᵒᵖ n ↦
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj (τ.obj 0))

/-- 単体圏の nerve の各次数は、評価関手の依存和と底に自然に同型。 -/
def transportSimplexNerveDegreeIso (n : ℕ) :
    transportSimplexNerveFunctor ⋙
        (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋n⦌) ≅
      transportSimplexNerveDegreeFamily n :=
  NatIso.ofComponents (fun B ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexChainEquiv B n).toIso) (by
    intro B D f
    apply ConcreteCategory.hom_ext
    intro σ
    rfl)

/-- 任意の小さい余極限 cocone は、単体圏の nerve で再び余極限 cocone となる。 -/
def transportSimplexNerveCoconeIsColimit {J : Type v} [SmallCategory J]
    {F : J ⥤ SSet.{max u v}} {c : Cocone F} (hc : IsColimit c) :
    IsColimit (transportSimplexNerveFunctor.mapCocone c) := by
  apply evaluationJointlyReflectsColimits
  rintro ⟨⟨n⟩⟩
  have hf : IsColimit ((transportSimplexNerveDegreeFamily n).mapCocone c) :=
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexShapeFamilyCoconeIsColimit
      (F := fun τ : ComposableArrows SimplexCategoryᵒᵖ n ↦
        F ⋙ (evaluation SimplexCategoryᵒᵖ (Type (max u v))).obj (τ.obj 0))
      (c := fun τ ↦ ((evaluation SimplexCategoryᵒᵖ (Type (max u v))).obj (τ.obj 0)).mapCocone c)
      (fun τ ↦
      isColimitOfPreserves ((evaluation SimplexCategoryᵒᵖ (Type (max u v))).obj (τ.obj 0)) hc)
  exact IsColimit.mapCoconeEquiv (transportSimplexNerveDegreeIso n).symm hf

/-- 単体圏の nerve 関手は、小余積・transfinite な付加を含む全ての小余極限を保つ。 -/
instance transportSimplexNerveFunctor_preservesColimits :
    PreservesColimitsOfSize.{u, u} transportSimplexNerveFunctor.{u} where
  preservesColimitsOfShape := fun {_J} _ ↦ {
    preservesColimit := fun {_F} ↦ {
      preserves := fun {_c} hc ↦ ⟨transportSimplexNerveCoconeIsColimit hc⟩ } }

/-- 単体圏の nerve 関手は、底の単射を単射に写す。 -/
instance transportSimplexNerveFunctor_preservesMonomorphisms :
    transportSimplexNerveFunctor.{u}.PreservesMonomorphisms where
  preserves f _ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexNerveMap_mono f

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
