module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerHom
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
概要：標的の厳密な同型による後合成は、指定関手同型の等式を反映する。
方針：内部 Hom とホモトピー圏に同型を写し、忠実性を使う。
規約：異なる端点表示には端点の等式を明示。使われ方：共通点同型の後合成の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 厳密な標的同型の後合成は、全関手空間のホモトピー圏で忠実。 -/
lemma functorPostcompIso_faithful (A : SSet.{u}) {X Y : SSet.{u}} (e : X ≅ Y) :
    (SSet.mapHomotopyCategory ((ihom A).map e.hom)).Faithful :=
  (Cat.equivOfIso (hoFunctor.mapIso ((ihom A).mapIso e))).fullyFaithfulFunctor.faithful

/-- 同じ二射間の指定同型の値は、標的同型で後合成した値から回収できる。 -/
lemma functorIso_postcomp_injective_iso {A X Y : SSet.{u}} (e : X ≅ Y) {f g : A ⟶ X} :
    Function.Injective (fun d : FunctorIso f g => d.postcomp e.hom) := by
  have := functorPostcompIso_faithful A e
  intro d d' h
  apply Iso.ext
  apply (SSet.mapHomotopyCategory ((ihom A).map e.hom)).map_injective
  have hm := congrArg (fun k => k.hom) h
  dsimp only at hm
  simpa only [functorIso_postcomp_hom] using hm

/-- 元の端点の等式を与えれば、標的同型で後合成した型付き一致も反映できる。 -/
lemma functorIso_postcomp_iso_reflects_heq {A X Y : SSet.{u}} (e : X ≅ Y)
    {f g f' g' : A ⟶ X} (a : FunctorIso f g) (b : FunctorIso f' g')
    (hf : f = f') (hg : g = g') (h : HEq (a.postcomp e.hom) (b.postcomp e.hom)) :
    HEq a b := by
  subst f' g'
  exact heq_of_eq (functorIso_postcomp_injective_iso e (eq_of_heq h))

end SerrePositivity.InfinityCategories.F2
