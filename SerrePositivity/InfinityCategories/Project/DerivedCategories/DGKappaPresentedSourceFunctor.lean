module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceInputHomLaws
/-!
概要：κ-small 出発提示表示への作用を、入力 dg 関手圏からの実 dg 関手へ束ねる。
方針：全パラメータ自然変換を小さい表示型上の Hom end へ戻し、評価で法則を検証する。
規約：入力の dg 自然変換を離散化しない。後合成の厳密則は別の入口で検証する。
使われ方：16時間試作の入力関手 nerve 上の高次作用の入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded _root_.SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D E : Type u)
  [DGCategory R D] [DGCategory R E] (κ : Cardinal.{u})

def dgKappaPresentedSourceActionHom (F G : DGFunctor R D E) :
    dgFunctorHom R D E F G ⟶
      dgFunctorHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R E κ)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ G) :=
  (dgFunctorHomEquiv R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R E κ)
    (dgFunctorHom R D E F G) _ _).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceParameter R D E κ
        (dgFunctorHomEquiv R D E (dgFunctorHom R D E F G) F G (𝟙 _)))

lemma dgKappaPresentedSourceActionHom_π (F G : DGFunctor R D E)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) :
    dgKappaPresentedSourceActionHom R D E κ F G ≫
      dgFunctorHomπ R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R E κ)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ G) X =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceInputHom R D E κ F G X :=
  dgFunctorHomEquiv_symm_π _ _ _ _ _ _ _ _

/-- 入力の全次数自然変換を保つ、出発提示表示への元の実 dg 作用。 -/
def dgKappaPresentedSourceFunctor :
    DGFunctor R (DGFunctor R D E)
      (DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R E κ)) where
  obj F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ F
  map := dgKappaPresentedSourceActionHom R D E κ
  map_id F := by
    apply dgFunctorHom_ext
    intro X
    rw [Category.assoc, dgKappaPresentedSourceActionHom_π]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceInputHom_identity R D E κ F X).trans
      (dgFunctorIdentity_π R _ _ _ X).symm
  map_comp F G H := by
    change dgFunctorComposition R D E F G H ≫ dgKappaPresentedSourceActionHom R D E κ F H =
      (dgKappaPresentedSourceActionHom R D E κ F G ⊗ₘ
        dgKappaPresentedSourceActionHom R D E κ G H) ≫
          dgFunctorComposition R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R E κ)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ G)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ H)
    apply dgFunctorHom_ext
    intro X
    simp only [Category.assoc, dgKappaPresentedSourceActionHom_π, dgFunctorComposition_π,
      tensorHom_comp_tensorHom_assoc]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceInputHom_composition R D E κ F G H X

end SerrePositivity.InfinityCategories.Project.DerivedCategories
