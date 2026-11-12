module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyNerveExponential
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-!
概要：通常関手の nerve の写像空間における充満忠実性から、通常の充満忠実性を戻す。
方針：h への充満忠実性と、nerve 随伴の可逆余単位の自然性を使う。
規約：始域・終域の通常圏を保持する。使われ方：局所化の h 圏上の自然変換の一意性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def fullyFaithful_of_nerveMap {A B : Type u} [Category.{u} A] [Category.{u} B]
    (F : A ⥤ B) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (nerveMap F)) : F.FullyFaithful := by
  let eA := Cat.equivOfIso (nerveFunctorCompHoFunctorIso.app (Cat.of A))
  let eB := Cat.equivOfIso (nerveFunctorCompHoFunctorIso.app (Cat.of B))
  have h : (hoFunctor.map (nerveMap F)).toFunctor ⋙ eB.functor = eA.functor ⋙ F := by
    exact congrArg Cat.Hom.toFunctor (nerveFunctorCompHoFunctorIso.hom.naturality F.toCatHom)
  have hf := hF.toHoFullyFaithful.comp eB.fullyFaithfulFunctor
  rw [h] at hf
  have hg := eA.fullyFaithfulInverse.comp hf
  exact hg.ofIso ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eA.counitIso F ≪≫ F.leftUnitor)

end SerrePositivity.KST.LocalizingInvariants
