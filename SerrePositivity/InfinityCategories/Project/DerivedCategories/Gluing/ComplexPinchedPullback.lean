module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PinchedPullbackPreservation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexPinchedModel

/-! 同じ自然な単位 Hom 同型を通し、任意複体の空間模型の引き戻し保存を得る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory DifferentialGraded
variable {R : Type u} [CommRing R] {P Q T U : Complex R}
  {a : P ⟶ Q} {b : P ⟶ T} {f : Q ⟶ U} {g : T ⟶ U}

lemma dgGluingComplexUnitHom_isPullback (h : IsPullback a b f g) :
    IsPullback (homPostcompose (𝟙_ (Complex R)) a) (homPostcompose (𝟙_ (Complex R)) b)
      (homPostcompose (𝟙_ (Complex R)) f) (homPostcompose (𝟙_ (Complex R)) g) :=
  h.of_iso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso T) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso U)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso_naturality a).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso_naturality b).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso_naturality f).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso_naturality g).symm

lemma dgGluingComplexPinchedMap_isPullback (h : IsPullback a b f g) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} b)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} g) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedChainMap_isPullback (dgGluingComplexUnitHom_isPullback h)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
