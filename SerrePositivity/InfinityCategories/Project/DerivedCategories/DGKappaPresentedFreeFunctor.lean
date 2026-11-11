module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeInputHomLaws
/-!
概要：κ-small 自由表示への作用を、入力 dg 関手圏からの実 dg 関手へ束ねる。
方針：全パラメータ自然変換を小さい表示型上の Hom end へ戻し、評価で法則を検証する。
規約：入力の dg 自然変換を離散化しない。後合成の厳密則は別項目。
使われ方：16時間試作の入力関手 nerve 上の高次作用の入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded _root_.SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D : Type v) (E : Type w)
  [DGCategory R D] [DGCategory R E] [Small.{u} D] [Small.{u} E] (κ : Cardinal.{u})

def dgKappaPresentedFreeActionHom (F G : DGFunctor R D E) :
    dgFunctorHom R D E F G ⟶
      dgFunctorHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject E κ)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeAction R D E F κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeAction R D E G κ) :=
  (dgFunctorHomEquiv R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject E κ)
    (dgFunctorHom R D E F G) _ _).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeParameter R D E κ
        (dgFunctorHomEquiv R D E (dgFunctorHom R D E F G) F G (𝟙 _)))

lemma dgKappaPresentedFreeActionHom_π (F G : DGFunctor R D E)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) :
    dgKappaPresentedFreeActionHom R D E κ F G ≫
      dgFunctorHomπ R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject E κ)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeAction R D E F κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeAction R D E G κ) X =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeInputHom R D E κ F G X :=
  dgFunctorHomEquiv_symm_π _ _ _ _ _ _ _ _

/-- 入力の全次数自然変換を保つ、自由表示への元の実 dg 作用。 -/
def dgKappaPresentedFreeFunctor :
    DGFunctor R (DGFunctor R D E)
      (DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject E κ)) where
  obj F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeAction R D E F κ
  map := dgKappaPresentedFreeActionHom R D E κ
  map_id F := by
    apply dgFunctorHom_ext
    intro X
    rw [Category.assoc, dgKappaPresentedFreeActionHom_π]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeInputHom_identity R D E κ F X).trans
      (dgFunctorIdentity_π R _ _ _ X).symm
  map_comp F G H := by
    change dgFunctorComposition R D E F G H ≫ dgKappaPresentedFreeActionHom R D E κ F H =
      (dgKappaPresentedFreeActionHom R D E κ F G ⊗ₘ
        dgKappaPresentedFreeActionHom R D E κ G H) ≫
          dgFunctorComposition R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject E κ)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeAction R D E F κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeAction R D E G κ)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeAction R D E H κ)
    apply dgFunctorHom_ext
    intro X
    simp only [Category.assoc, dgKappaPresentedFreeActionHom_π, dgFunctorComposition_π,
      tensorHom_comp_tensorHom_assoc]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeInputHom_composition R D E κ F G H X

end SerrePositivity.InfinityCategories.Project.DerivedCategories
