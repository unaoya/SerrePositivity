module
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestriction
public import SerrePositivity.DifferentialGraded.Bimodule.Uncurry

/-! # 中間dg圏の左右制限のuncurryHomと積dg関手のHom写像 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)

omit [Small.{u} C] [Small.{u} D] [DGCategory A E] in
lemma leftRestriction_uncurryHom (P : Bimodule A B C) (x y : DGTensorCategory A Bᵒᵖ D) :
    (leftRestriction A B C D F P).uncurryHom x y =
      (𝟙 (x.1 ⟶[Complex A] y.1) ⊗ₘ F.map x.2 y.2) ≫
        P.uncurryHom (x.1, F.obj x.2) (y.1, F.obj y.2) := by
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change ((leftRestriction A B C D F P).uncurryHom x y).f n (dgTensorElement A f g hn) =
    (P.uncurryHom (x.1, F.obj x.2) (y.1, F.obj y.2)).f n
      ((𝟙 (x.1 ⟶[Complex A] y.1) ⊗ₘ F.map x.2 y.2).f n (dgTensorElement A f g hn))
  have ht := tensorMap_apply (𝟙 (x.1 ⟶[Complex A] y.1)) (F.map x.2 y.2) p q n hn f g
  change (𝟙 (x.1 ⟶[Complex A] y.1) ⊗ₘ F.map x.2 y.2).f n
    (dgTensorElement A f g hn) = dgTensorElement A (x := (x.1, F.obj x.2)) (y := (y.1, F.obj y.2))
      f ((F.map x.2 y.2).f q g) hn at ht
  have he := congrArg (fun t => (P.uncurryHom (x.1, F.obj x.2) (y.1, F.obj y.2)).f n t) ht
  refine Eq.trans ?_ he.symm
  rw [uncurryHom_apply, uncurryHom_apply]
  rfl

lemma rightRestriction_uncurryHom (Q : Bimodule A C E) (x y : DGTensorCategory A Dᵒᵖ E) :
    (rightRestriction A C D E F Q).uncurryHom x y =
      (F.op.map x.1 y.1 ⊗ₘ 𝟙 (x.2 ⟶[Complex A] y.2)) ≫
        Q.uncurryHom (F.op.obj x.1, x.2) (F.op.obj y.1, y.2) := by
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change ((rightRestriction A C D E F Q).uncurryHom x y).f n (dgTensorElement A f g hn) =
    (Q.uncurryHom (F.op.obj x.1, x.2) (F.op.obj y.1, y.2)).f n
      ((F.op.map x.1 y.1 ⊗ₘ 𝟙 (x.2 ⟶[Complex A] y.2)).f n (dgTensorElement A f g hn))
  have ht := tensorMap_apply (F.op.map x.1 y.1) (𝟙 (x.2 ⟶[Complex A] y.2)) p q n hn f g
  change (F.op.map x.1 y.1 ⊗ₘ 𝟙 (x.2 ⟶[Complex A] y.2)).f n
    (dgTensorElement A f g hn) =
      dgTensorElement A (x := (F.op.obj x.1, x.2)) (y := (F.op.obj y.1, y.2))
      ((F.op.map x.1 y.1).f p f) g hn at ht
  have he := congrArg (fun t => (Q.uncurryHom (F.op.obj x.1, x.2) (F.op.obj y.1, y.2)).f n t) ht
  refine Eq.trans ?_ he.symm
  rw [uncurryHom_apply, uncurryHom_apply]
  have hl : (rightRestriction A C D E F Q).leftCochain g y.1.unop =
      Q.leftCochain g (F.obj y.1.unop) :=
    congrArg (fun k => k.f q g) (rightRestriction_leftAt_map A C D E F Q y.1.unop x.2 y.2)
  rw [hl]
  rfl

end SerrePositivity.DifferentialGraded.Bimodule
