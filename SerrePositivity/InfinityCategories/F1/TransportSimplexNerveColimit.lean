module

public import SerrePositivity.InfinityCategories.F1.SimplexShapeFamilyColimit
public import SerrePositivity.InfinityCategories.F1.TransportSimplexNervePushout

/-!
概要：単体圏の nerve は小さい余極限を全て保存する。
方針：各次数を射列の形で添字付けた評価関手の依存和と自然に同定する。
規約：底や図式の射に充填性・単射性を要求しない。
使われ方：小余積と transfinite なセル付加で反転関手を極限表示する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 底の単体集合を、その単体圏の実際の nerve へ送る関手。 -/
def transportSimplexNerveFunctor : SSet.{u} ⥤ SSet.{u} where
  obj B := nerve (TransportSimplexCategory B)
  map f := nerveMap (transportSimplexFunctor f)
  map_id B := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    change σ ⋙ transportSimplexFunctor (𝟙 B) = σ
    rw [transportSimplexFunctor_id, Functor.comp_id]
  map_comp f g := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    change σ ⋙ transportSimplexFunctor (f ≫ g) =
      (σ ⋙ transportSimplexFunctor f) ⋙ transportSimplexFunctor g
    rw [transportSimplexFunctor_comp, Functor.assoc]

/-- 一定次数の射列座標を与える、評価関手の依存和。 -/
def transportSimplexNerveDegreeFamily (n : ℕ) : SSet.{u} ⥤ Type u :=
  simplexShapeFamilyDiagram (fun τ : ComposableArrows SimplexCategoryᵒᵖ n ↦
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj (τ.obj 0))

/-- 単体圏の nerve の各次数は、評価関手の依存和と底に自然に同型。 -/
def transportSimplexNerveDegreeIso (n : ℕ) :
    transportSimplexNerveFunctor ⋙
        (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋n⦌) ≅
      transportSimplexNerveDegreeFamily n :=
  NatIso.ofComponents (fun B ↦ (transportSimplexChainEquiv B n).toIso) (by
    intro B D f
    apply ConcreteCategory.hom_ext
    intro σ
    rfl)

/-- 任意の小さい余極限 cocone は、単体圏の nerve で再び余極限 cocone となる。 -/
def transportSimplexNerveCoconeIsColimit {J : Type u} [SmallCategory J]
    {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c) :
    IsColimit (transportSimplexNerveFunctor.mapCocone c) := by
  apply evaluationJointlyReflectsColimits
  rintro ⟨⟨n⟩⟩
  have hf : IsColimit ((transportSimplexNerveDegreeFamily n).mapCocone c) :=
    simplexShapeFamilyCoconeIsColimit
      (F := fun τ : ComposableArrows SimplexCategoryᵒᵖ n ↦
        F ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj (τ.obj 0))
      (c := fun τ ↦ ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (τ.obj 0)).mapCocone c)
      (fun τ ↦
      isColimitOfPreserves ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (τ.obj 0)) hc)
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
  preserves f _ := transportSimplexNerveMap_mono f

end SerrePositivity.InfinityCategories
