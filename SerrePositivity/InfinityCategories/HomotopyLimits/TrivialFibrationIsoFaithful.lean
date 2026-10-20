module

public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyIsoPostcomp
public import SerrePositivity.InfinityCategories.Core.MappingSpaceTrivialFibration
public import SerrePositivity.InfinityCategories.Core.FullyFaithful

/-!
概要：自明 Kan 射による後合成で同じ射になる関手同型は、元の同じ射を持つ。
方針：内部 Hom 上の自明 Kan 性から h Fun の充満忠実性を使う。
規約：両端の関手を固定し、像の Arrow の等式を要求する。使われ方：評価固定代表の類。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 自明 Kan 射への後合成で同じ Arrow になる同型は、元の h Fun でも同じ射。 -/
lemma trivialKanFibration_postcomp_iso_hom_injective {T E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p]
    {a b : T ⟶ E} (I J : FunctorIso a b)
    (h : Arrow.mk (FunctorIso.postcomp I p).hom = Arrow.mk (FunctorIso.postcomp J p).hom) :
    I.hom = J.hom := by
  have hf := (isFullyFaithful_of_trivialKanFibration ((ihom T).map p)).toHoFullyFaithful
  apply hf.map_injective
  rw [functorIso_postcomp_hom, functorIso_postcomp_hom] at h
  obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

end SerrePositivity.InfinityCategories.HomotopyLimits
