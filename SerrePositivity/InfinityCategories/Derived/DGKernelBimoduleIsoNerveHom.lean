module
public import SerrePositivity.InfinityCategories.Derived.DGKernelTensorIsoNerveAlgebra
/-!
概要：指定双加群同型の通常 kernel 作用を、同じ composeMap の全関手射へ戻す。
方針：既存の同型を回収する実関手と、その同じ射への作用を使う。
規約：指定同型を変更しない。使われ方：通常 kernel の五角式の終辺。
-/
@[expose] public section
open CategoryTheory
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 元の双加群同型の通常 kernel 作用の射は、同じ composeMap の実像。 -/
lemma dgKernelTensorIsoNerveOfBimoduleIso_hom {P Q : BimoduleCategory R E D}
    (e : P ≅ Q) :
    (dgKernelTensorIsoNerveOfBimoduleIso R D E e).hom =
      (dgBimoduleFunctorHomFunctor R E (RightModule R D)).map
        (BimoduleTensor.composeMap R E D (RightModule R D) e.hom
          (𝟙 (BimoduleCategory.of R D (RightModule R D) (DGFunctor.id (RightModule R D))))) := by
  rw [← dgKernelTensorFunctorHomFunctor_mapIso]
  rfl
end
end SerrePositivity.InfinityCategories
