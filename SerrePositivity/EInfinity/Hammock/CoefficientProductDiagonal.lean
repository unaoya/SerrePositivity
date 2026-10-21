module

public import SerrePositivity.EInfinity.Hammock.CoefficientProductRelative
public import SerrePositivity.EInfinity.Hammock.DoubleSimplicialDiagonal
public import SerrePositivity.EInfinity.Hammock.WeakTensor

/-!
# 元の係数積の対角 nerve と弱比較

概要：元の積圏の射列を二つの射列へ戻し、同じ対角比較の弱同値性を証明する。
方針：全単体の積と射影の厳密な往復、元の写像との正方形を使う。
規約：各次数の比較射の弱同値性は仮定せず、両対角の弱同値性だけを入力する。
使われ方：混合二方向の係数積の対角比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.CoefficientProduct
open CategoryTheory MonoidalCategory SerrePositivity.InfinityCategories
variable (P Q : SimplicialObject Cat.{u, u})
def diagonalNerveIso :
    DoubleSimplicial.diagonalFunctor.obj (diagram P Q ⋙ nerveFunctor) ≅
      DoubleSimplicial.diagonalFunctor.obj (P ⋙ nerveFunctor) ⊗
        DoubleSimplicial.diagonalFunctor.obj (Q ⋙ nerveFunctor) where
  hom :=
    { app n := ↾fun σ => (σ ⋙ CategoryTheory.Prod.fst (P.obj n) (Q.obj n),
        σ ⋙ CategoryTheory.Prod.snd (P.obj n) (Q.obj n))
      naturality n m θ := by
        apply ConcreteCategory.hom_ext
        intro σ
        rfl }
  inv :=
    { app n := ↾fun p => p.1.prod' p.2
      naturality n m θ := by
        apply ConcreteCategory.hom_ext
        intro p
        rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro p
    rfl
variable {P Q} {P' Q' : SimplicialObject Cat.{u, u}}
  (α : P ⟶ P') (β : Q ⟶ Q')
lemma diagonalNerveIso_naturality :
    DoubleSimplicial.diagonalFunctor.map
        (Functor.whiskerRight (change (𝟭 _) α β) nerveFunctor) ≫
      (diagonalNerveIso P' Q').hom =
    (diagonalNerveIso P Q).hom ≫
      (DoubleSimplicial.diagonalFunctor.map (Functor.whiskerRight α nerveFunctor) ⊗ₘ
        DoubleSimplicial.diagonalFunctor.map (Functor.whiskerRight β nerveFunctor)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  rfl
lemma diagonalMap_weak
    (hα : IsWeakHomotopyEquivalence
      (DoubleSimplicial.diagonalFunctor.map (Functor.whiskerRight α nerveFunctor)))
    (hβ : IsWeakHomotopyEquivalence
      (DoubleSimplicial.diagonalFunctor.map (Functor.whiskerRight β nerveFunctor))) :
    IsWeakHomotopyEquivalence (DoubleSimplicial.diagonalFunctor.map
      (Functor.whiskerRight (change (𝟭 _) α β) nerveFunctor)) := by
  have h := (isPrecompositionEquivalence_of_iso
    (diagonalNerveIso P Q)).isWeakHomotopyEquivalence.comp (weakTensor hα hβ)
  rw [← diagonalNerveIso_naturality] at h
  exact (isPrecompositionEquivalence_of_iso
    (diagonalNerveIso P' Q')).isWeakHomotopyEquivalence.cancel_right h
end SerrePositivity.EInfinity.Hammock.CoefficientProduct
