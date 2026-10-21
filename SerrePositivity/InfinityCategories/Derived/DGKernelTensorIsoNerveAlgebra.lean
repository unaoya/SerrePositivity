module
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleIsoNerveAlgebra
public import SerrePositivity.InfinityCategories.Derived.DGKernelBimoduleIso
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 元の kernel を、同じ通常 tensor の加群値双加群へ送る関手。 -/
def dgKernelActionBimoduleFunctor :
    BimoduleCategory R E D ⥤ BimoduleCategory R E (RightModule R D) :=
  ((𝟭 (BimoduleCategory R E D)).prod'
      ((Functor.const (BimoduleCategory R E D)).obj
        (BimoduleCategory.of R D (RightModule R D) (DGFunctor.id (RightModule R D))))) ⋙
    BimoduleTensor.composeFunctor R E D (RightModule R D)
/-- 元の kernel 射を、その通常 tensor の実 dg nerve 間の h Fun の射へ送る関手。 -/
def dgKernelTensorFunctorHomFunctor :
    BimoduleCategory R E D ⥤
      hoFunctor.obj ((ihom (dgNerve R (RightModule R D))).obj
        (dgNerve R (RightModule R E))) :=
  dgKernelActionBimoduleFunctor R D E ⋙ dgBimoduleFunctorHomFunctor R E (RightModule R D)
/-- 同じ関手で写した同型は、元の通常 tensor の指定 nerve 比較そのもの。 -/
lemma dgKernelTensorFunctorHomFunctor_mapIso {P Q : BimoduleCategory R E D} (e : P ≅ Q) :
    (dgKernelTensorFunctorHomFunctor R D E).mapIso e =
      dgKernelTensorIsoNerveOfBimoduleIso R D E e := by
  let J := BimoduleCategory.of R D (RightModule R D) (DGFunctor.id (RightModule R D))
  have he : (dgKernelActionBimoduleFunctor R D E).mapIso e =
      (BimoduleTensor.composeFunctor R E D (RightModule R D)).mapIso
        (Iso.prod e (Iso.refl J)) := by
    apply Iso.ext
    rfl
  change (dgBimoduleFunctorHomFunctor R E (RightModule R D)).mapIso
      ((dgKernelActionBimoduleFunctor R D E).mapIso e) = _
  rw [he, dgBimoduleFunctorHomFunctor_mapIso]
  rfl
/-- 元の通常 tensor の指定 nerve 比較は恒等を保つ。 -/
lemma dgKernelTensorIsoNerveOfBimoduleIso_refl (P : BimoduleCategory R E D) :
    dgKernelTensorIsoNerveOfBimoduleIso R D E (Iso.refl P) = Iso.refl _ := by
  rw [← dgKernelTensorFunctorHomFunctor_mapIso]
  exact Functor.mapIso_refl _ _
/-- 元の通常 tensor の指定 nerve 比較は通常順合成を保つ。 -/
lemma dgKernelTensorIsoNerveOfBimoduleIso_trans {P Q S : BimoduleCategory R E D}
    (e : P ≅ Q) (f : Q ≅ S) :
    dgKernelTensorIsoNerveOfBimoduleIso R D E (e ≪≫ f) =
      dgKernelTensorIsoNerveOfBimoduleIso R D E e ≪≫
        dgKernelTensorIsoNerveOfBimoduleIso R D E f := by
  rw [← dgKernelTensorFunctorHomFunctor_mapIso, ← dgKernelTensorFunctorHomFunctor_mapIso,
    ← dgKernelTensorFunctorHomFunctor_mapIso]
  exact Functor.mapIso_trans _ _ _
/-- 元の通常 tensor の指定 nerve 比較は指定逆同型を保つ。 -/
lemma dgKernelTensorIsoNerveOfBimoduleIso_symm {P Q : BimoduleCategory R E D} (e : P ≅ Q) :
    dgKernelTensorIsoNerveOfBimoduleIso R D E e.symm =
      (dgKernelTensorIsoNerveOfBimoduleIso R D E e).symm := by
  rw [← dgKernelTensorFunctorHomFunctor_mapIso, ← dgKernelTensorFunctorHomFunctor_mapIso]
  exact Functor.mapIso_symm _ _
end SerrePositivity.InfinityCategories
