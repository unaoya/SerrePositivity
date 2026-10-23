module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallInternalHomContinuity
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredKanCocone
public import SerrePositivity.InfinityCategories.F1.KanPointHomEnriched

/-!
概要：μ-small な Kan 対象からの全内部 Hom と、μ-filtered Kan 図式の余極限の保存。
方針：任意の始点の豊穣 Hom 自己関手を構成し、同じ strict 全余錐へ内部 Hom の連続性を適用する。
規約：全高次射への作用を保持。ここでは一般の coherent な全図式に対する compact 性はまだ主張しない。
使われ方：前層の compact 生成圏に向けた、小さい空間の compact 性の strict 模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 任意の小さい Kan 始点からの内部 Hom を取る、全高次射の作用を持つ豊穣自己関手。 -/
def kanInternalHomEnriched (K : KanObject.{u}) :
    EnrichedFunctor SSet.{u} KanObject.{u} KanObject.{u} where
  obj L := ⟨(ihom K.obj).obj L.obj, inferInstance⟩
  map L M := curry (MonoidalClosed.comp K.obj L.obj M.obj)
  map_id L := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, t⟩
    apply Functor.HomObj.ext
    funext m α
    apply ConcreteCategory.hom_ext
    intro x
    change f.app m (α ≫ 𝟙 m) x = f.app m α x
    rw [Category.comp_id]
  map_comp L M N := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g, h⟩
    apply Functor.HomObj.ext
    funext m α
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- 同じ全豊穣 Hom 自己関手を、元の空間 ∞ 圏の全関手として実現する。 -/
def kanInternalHomInfinity (K : KanObject.{u}) : SpaceInfinity.{u} ⟶ SpaceInfinity.{u} :=
  coherentNerveMap (kanInternalHomEnriched K)

/-- 同じ Kan 内部 Hom の通常の全図式への作用。 -/
def kanInternalHomFunctor (K : KanObject.{u}) : KanObject.{u} ⥤ KanObject.{u} where
  obj L := (kanInternalHomEnriched K).obj L
  map f := (ihom K.obj).map f
  map_id L := (ihom K.obj).map_id L.obj
  map_comp f g := (ihom K.obj).map_comp f g

/-- 内部 Hom を取った同じ strict 全余錐は、忘却後も μ-filtered 余極限である。 -/
def smallKanHom_mapCocone_isColimit {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) (K : KanObject.{u}) (hK : IsKappaSmall μ K.obj)
    {J : Type u} [SmallCategory J] [IsCardinalFiltered J μ]
    {F : J ⥤ KanObject.{u}} (c : Cocone F) (hc : IsColimit (kanObjectForget.mapCocone c)) :
    IsColimit (kanObjectForget.mapCocone ((kanInternalHomFunctor K).mapCocone c)) := by
  have := smallInternalHom_preservesCardinalFilteredColimits hμ K.obj hK J
  exact isColimitOfPreserves (ihom K.obj) hc

/-- 同じ内部 Hom の strict 全余錐は、元の空間 ∞ 圏でも native な余極限となる。 -/
lemma smallKanHom_mapCocone_native {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) (K : KanObject.{u}) (hK : IsKappaSmall μ K.obj)
    {J : Type u} [SmallCategory J] [IsCardinalFiltered J μ]
    {F : J ⥤ KanObject.{u}} (c : Cocone F) (hc : IsColimit (kanObjectForget.mapCocone c)) :
    IsColimitCone (HomotopyLimits.strictNativeCocone ((kanInternalHomFunctor K).mapCocone c)) := by
  have := isFiltered_of_isCardinalFiltered J μ
  exact Ind.strictNativeCocone_isColimit_of_filtered_forget _
    (smallKanHom_mapCocone_isColimit hμ K hK c hc)

end SerrePositivity.InfinityCategories.F2.Presentable
