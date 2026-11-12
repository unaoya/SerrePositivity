module

public import SerrePositivity.HomologicalAlgebra.ProjectiveFreePresheaf
import all Mathlib.CategoryTheory.Generator.Presheaf

/-!
# 自由表現可能前層の全関手

## 概要
指定した係数対象の余積を取り、Yoneda の全関手を自由表現可能前層の全関手へ移す。

## 方針
型から係数の余積への関手を Yoneda に後合成し、元の自由 Yoneda の定義と照合する。

## 規約
対象と射の選択をし直さず、同じ余積と同じ添字写像を使う。

## 使われ方
Weibel §2.2、HA 1.2.4。標準単体の線形重みを射影的な各項を持つ単体的前層へ送る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u v' u'
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u'} [Category.{v'} C] [HasCoproducts.{v} C]

/-- 各型に、その型で添字づけた指定係数 P の余積を割り当てる関手。 -/
def copowerFunctor (P : C) : Type v ⥤ C where
  obj T := ∐ (fun _ : T => P)
  map f := Sigma.map' f (fun _ => 𝟙 P)
  map_id _ := Sigma.map'_id_id
  map_comp f g := by
    apply Sigma.hom_ext
    intro t
    simp

/-- Yoneda の全対象・全射を、同じ係数の自由表現可能前層へ送る。 -/
def freePresheafFunctor (J : Type u) [Category.{v} J] (P : C) : J ⥤ Jᵒᵖ ⥤ C :=
  yoneda ⋙ (Functor.whiskeringRight Jᵒᵖ (Type v) C).obj (copowerFunctor P)

/-- 各値は既存の自由 Yoneda 前層と、元の余積と添字作用を共有する。 -/
def freePresheafFunctorObjIso (J : Type u) [Category.{v} J] (P : C) (j : J) :
    (freePresheafFunctor J P).obj j ≅ Presheaf.freeYoneda j P := Iso.refl _

/-- 射影係数のとき、全関手の各値は前層圏で射影的。 -/
theorem freePresheafFunctor_projective (J : Type u) [Category.{v} J]
    [HasPushouts C] (P : C) [Projective P] (j : J) :
    Projective ((freePresheafFunctor J P).obj j) :=
  Projective.of_iso (freePresheafFunctorObjIso J P j).symm (freeYoneda_projective j P)

end SerrePositivity.HomologicalAlgebra
