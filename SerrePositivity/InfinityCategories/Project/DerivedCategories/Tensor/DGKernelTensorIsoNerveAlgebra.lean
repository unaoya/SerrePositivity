module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGBimoduleIsoNerveAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelBimoduleIso
/-!
概要：元の通常 tensor の実 nerve 比較は、元の双加群射に関手的で恒等・合成・逆を保つ。
方針：同じ通常 tensor の双関手と、実 nerve 写像による h Fun の関手を合成する。
規約：既存の指定比較を等式で回収する。使われ方：導来 kernel 比較の coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の kernel を、同じ通常 tensor の加群値双加群へ送る関手。 -/
def dgKernelActionBimoduleFunctor :
    _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E (_root_.SerrePositivity.DifferentialGraded.RightModule R D) :=
  ((𝟭 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D)).prod'
      ((Functor.const (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D)).obj
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))))) ⋙
    _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeFunctor R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
/-- 元の kernel 射を、その通常 tensor の実 dg nerve 間の h Fun の射へ送る関手。 -/
def dgKernelTensorFunctorHomFunctor :
    _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D ⥤
      hoFunctor.obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R E))) :=
  dgKernelActionBimoduleFunctor R D E ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R E (RightModule R D)
/-- 同じ関手で写した同型は、元の通常 tensor の指定 nerve 比較そのもの。 -/
lemma dgKernelTensorFunctorHomFunctor_mapIso {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ Q) :
    (dgKernelTensorFunctorHomFunctor R D E).mapIso e =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E e := by
  let J := _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))
  have he : (dgKernelActionBimoduleFunctor R D E).mapIso e =
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeFunctor R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D)).mapIso
        (Iso.prod e (Iso.refl J)) := by
    apply Iso.ext
    rfl
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R E (RightModule R D)).mapIso
      ((dgKernelActionBimoduleFunctor R D E).mapIso e) = _
  rw [he, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor_mapIso]
  rfl
/-- 元の通常 tensor の指定 nerve 比較は恒等を保つ。 -/
lemma dgKernelTensorIsoNerveOfBimoduleIso_refl (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E (Iso.refl P) = Iso.refl _ := by
  rw [← dgKernelTensorFunctorHomFunctor_mapIso]
  exact Functor.mapIso_refl _ _
/-- 元の通常 tensor の指定 nerve 比較は通常順合成を保つ。 -/
lemma dgKernelTensorIsoNerveOfBimoduleIso_trans {P Q S : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D}
    (e : P ≅ Q) (f : Q ≅ S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E (e ≪≫ f) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E e ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E f := by
  rw [← dgKernelTensorFunctorHomFunctor_mapIso, ← dgKernelTensorFunctorHomFunctor_mapIso,
    ← dgKernelTensorFunctorHomFunctor_mapIso]
  exact Functor.mapIso_trans _ _ _
/-- 元の通常 tensor の指定 nerve 比較は指定逆同型を保つ。 -/
lemma dgKernelTensorIsoNerveOfBimoduleIso_symm {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E e.symm =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E e).symm := by
  rw [← dgKernelTensorFunctorHomFunctor_mapIso, ← dgKernelTensorFunctorHomFunctor_mapIso]
  exact Functor.mapIso_symm _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
