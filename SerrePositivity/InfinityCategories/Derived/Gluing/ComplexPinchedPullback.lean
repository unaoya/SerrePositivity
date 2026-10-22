module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedPullbackPreservation
public import SerrePositivity.InfinityCategories.Derived.ComplexPinchedModel

/-! 同じ自然な単位 Hom 同型を通し、任意複体の空間模型の引き戻し保存を得る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded
variable {R : Type u} [CommRing R] {P Q T U : Complex R}
  {a : P ⟶ Q} {b : P ⟶ T} {f : Q ⟶ U} {g : T ⟶ U}

lemma dgGluingComplexUnitHom_isPullback (h : IsPullback a b f g) :
    IsPullback (homPostcompose (𝟙_ (Complex R)) a) (homPostcompose (𝟙_ (Complex R)) b)
      (homPostcompose (𝟙_ (Complex R)) f) (homPostcompose (𝟙_ (Complex R)) g) :=
  h.of_iso (complexUnitHomIso P) (complexUnitHomIso Q)
    (complexUnitHomIso T) (complexUnitHomIso U)
    (complexUnitHomIso_naturality a).symm (complexUnitHomIso_naturality b).symm
    (complexUnitHomIso_naturality f).symm (complexUnitHomIso_naturality g).symm

lemma dgGluingComplexPinchedMap_isPullback (h : IsPullback a b f g) :
    IsPullback (complexPinchedMap.{u, v} a) (complexPinchedMap.{u, v} b)
      (complexPinchedMap.{u, v} f) (complexPinchedMap.{u, v} g) :=
  dgGluingPinchedChainMap_isPullback (dgGluingComplexUnitHom_isPullback h)

end SerrePositivity.InfinityCategories
