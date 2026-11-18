module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseAlgebraAdjunction

/-!
# 微分を消した自由代数の比較と指定生成元

## 概要
Berger–Moerdijk §1 の自由代数の比較が、元の自由生成元の指定射を保つことを示す。

## 方針
左随伴の一意性で選んだ比較の単位の式を、複体上の随伴対応で読む。

## 規約
自由代数の比較の向きと単位を保持する。

## 使われ方
次数付きのセルの基底と実際の付加生成元の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Operad
open CategoryTheory MonoidalCategory DifferentialGraded
variable {A : Type u} [CommRing A] (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A)

@[simp]
lemma eraseAlgebra_carrier (X : P.Algebra) :
    (P.eraseAlgebra.obj X).carrier = (eraseDifferential A).obj X.carrier := rfl

@[simp]
lemma eraseAlgebra_map_hom {X Y : P.Algebra} (f : X ⟶ Y) :
    (P.eraseAlgebra.map f).hom = (eraseDifferential A).map f.hom := rfl

@[simp]
lemma eraseAlgebraAdjunction_unit_hom (X : P.Algebra) :
    (P.eraseAlgebraAdjunction.unit.app X).hom =
      (eraseDifferentialAdjunction A).unit.app X.carrier := rfl

/-- The free algebra comparison preserves the specified generating unit. -/
@[reassoc]
lemma eraseFreeAlgebraIso_unit (V : Complex A) :
    (eraseDifferential A).map (P.freeAlgebraAdjunction.unit.app V) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P.erase).map (P.eraseFreeAlgebraIso.hom.app V) =
        P.erase.freeAlgebraAdjunction.unit.app ((eraseDifferential A).obj V) := by
  let a := eraseDifferentialAdjunction A
  let R := cofreeCycles A
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (P.freeAlgebraAdjunction.comp P.eraseAlgebraAdjunction)
    (a.comp P.erase.freeAlgebraAdjunction) V
  simp only [Adjunction.comp_unit_app] at h
  change (P.freeAlgebraAdjunction.unit.app V ≫
      (P.eraseAlgebraAdjunction.unit.app (P.freeAlgebraFunctor.obj V)).hom) ≫
      R.map ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P.erase).map (P.eraseFreeAlgebraIso.hom.app V)) =
    a.unit.app V ≫ R.map (P.erase.freeAlgebraAdjunction.unit.app
      ((eraseDifferential A).obj V)) at h
  rw [eraseAlgebraAdjunction_unit_hom] at h
  apply (a.homEquiv _ _).injective
  simp only [a.homEquiv_unit, CategoryTheory.Functor.id_obj,
    CategoryTheory.Functor.map_comp]
  erw [a.unit_naturality_assoc]
  simp only [CategoryTheory.Functor.id_obj, Category.assoc] at h ⊢
  exact h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
  export _root_.SerrePositivity.EInfinity.Operad (eraseFreeAlgebraIso_unit)

/-- The inverse free algebra comparison recovers the original generating unit. -/
@[reassoc]
lemma eraseFreeAlgebraIso_inv_unit (V : Complex A) :
    P.erase.freeAlgebraAdjunction.unit.app ((eraseDifferential A).obj V) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P.erase).map (P.eraseFreeAlgebraIso.inv.app V) =
        (eraseDifferential A).map (P.freeAlgebraAdjunction.unit.app V) := by
  let U := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P.erase
  let e := P.eraseFreeAlgebraIso.app V
  have h := congrArg (fun k => k ≫ U.map e.inv) (P.eraseFreeAlgebraIso_unit V)
  erw [Category.assoc, ← U.map_comp, e.hom_inv_id, U.map_id, Category.comp_id] at h
  exact h.symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
  export _root_.SerrePositivity.EInfinity.Operad (eraseFreeAlgebraIso_inv_unit)

/-- The free algebra comparison intertwines the two specified free-forgetful correspondences. -/
lemma eraseFreeAlgebraIso_homEquiv (V : Complex A) (X : P.Algebra)
    (f : P.freeAlgebraFunctor.obj V ⟶ X) :
    P.erase.freeAlgebraAdjunction.homEquiv _ _
      (P.eraseFreeAlgebraIso.inv.app V ≫ P.eraseAlgebra.map f) =
        (eraseDifferential A).map (P.freeAlgebraAdjunction.homEquiv _ _ f) := by
  simp only [Adjunction.homEquiv_unit]
  change P.erase.freeAlgebraAdjunction.unit.app ((eraseDifferential A).obj V) ≫
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P.erase).map (P.eraseFreeAlgebraIso.inv.app V) ≫
      (eraseDifferential A).map f.hom) =
        (eraseDifferential A).map (P.freeAlgebraAdjunction.unit.app V ≫ f.hom)
  rw [eraseFreeAlgebraIso_inv_unit_assoc, CategoryTheory.Functor.map_comp]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
  export _root_.SerrePositivity.EInfinity.Operad (eraseFreeAlgebraIso_homEquiv)

end SerrePositivity.EInfinity.Operad
