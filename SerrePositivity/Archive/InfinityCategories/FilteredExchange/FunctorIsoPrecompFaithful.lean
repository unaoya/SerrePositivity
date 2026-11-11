module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerHom

/-!
概要：同値による前合成は、元の指定関手同型の等式を忠実に反映する。
方針：関手空間の同値が誘導するホモトピー圏上の忠実性を使う。
規約：指定同型の値を保持。使われ方：全 Hom 係数で検証した指定比較の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 同値による前合成は、quasicategory を標的とする指定関手同型の等式を反映する。 -/
lemma functorIso_precomp_injective_of_qCatEquivalence {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    (i : A ⟶ X) (hi : IsQCatEquivalence i) {f g : X ⟶ Y} :
    Function.Injective (fun e : FunctorIso f g => e.precomp i) := by
  have hp := hi.precompose Y
  let D := (hoFunctor.map ((pre i).app Y)).toFunctor
  haveI := hp.isFullyFaithful.toHoFullyFaithful.faithful
  intro e d h
  apply Iso.ext
  apply D.map_injective
  have hh := congrArg (fun z : FunctorIso (i ≫ f) (i ≫ g) => z.hom) h
  rw [functorIso_precomp_hom, functorIso_precomp_hom] at hh
  exact hh

end SerrePositivity.InfinityCategories.F2
