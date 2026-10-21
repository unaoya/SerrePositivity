module

public import SerrePositivity.EInfinity.Hammock.TwoSidedGrothendieckLeftComparison
public import SerrePositivity.EInfinity.Hammock.NerveWeakTransport

/-!
# 二方向の Grothendieck 構成の両係数の弱同値不変性

概要：左右の係数の成分ごとの nerve 弱同値は、元の全圏の係数比較関手を弱同値にする。
方針：左係数は左右交換の可換式で右係数へ移し、元の両射を合成する。
規約：元の底と全係数自然変換を保持し、遷移の不変性を要求しない。
使われ方：DK §9.6と単体的な係数不変性§10.4の基礎。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedGrothendieck
open CategoryTheory SerrePositivity.InfinityCategories

variable {W : Type u} [Category.{u} W] {F F' : Wᵒᵖ ⥤ Cat.{u, u}}
  {G G' : W ⥤ Cat.{u, u}}

lemma leftCoefficientMap_isWeakHomotopyEquivalence (G : W ⥤ Cat.{u, u}) (α : F ⟶ F')
    (hα : ∀ w, IsWeakHomotopyEquivalence (nerveMap (α.app w).toFunctor)) :
    IsWeakHomotopyEquivalence (nerveMap (leftCoefficientMap G α)) := by
  have hr := rightCoefficientMap_isWeakHomotopyEquivalence (dualLeft G)
    (Functor.whiskerRight α Cat.opFunctor)
    (fun w => nerveMap_op_isWeakHomotopyEquivalence _ (hα w))
  have h := (nerveMap_equivalence_isWeakHomotopyEquivalence (dualEquivalence F G)).comp
    (nerveMap_op_isWeakHomotopyEquivalence _ hr)
  change IsWeakHomotopyEquivalence (nerveMap (dualFunctor F G ⋙
    (rightCoefficientMap (dualLeft G) (Functor.whiskerRight α Cat.opFunctor)).op)) at h
  rw [← leftCoefficientMap_dualFunctor G α] at h
  change IsWeakHomotopyEquivalence (nerveMap (leftCoefficientMap G α) ≫
    nerveMap (dualFunctor F' G)) at h
  exact (nerveMap_equivalence_isWeakHomotopyEquivalence (dualEquivalence F' G)).cancel_right h

lemma coefficientMap_isWeakHomotopyEquivalence (α : F ⟶ F') (β : G ⟶ G')
    (hα : ∀ w, IsWeakHomotopyEquivalence (nerveMap (α.app w).toFunctor))
    (hβ : ∀ w, IsWeakHomotopyEquivalence (nerveMap (β.app w).toFunctor)) :
    IsWeakHomotopyEquivalence (nerveMap (coefficientMap α β)) := by
  rw [coefficientMap_factorization G α β]
  change IsWeakHomotopyEquivalence (nerveMap (rightCoefficientMap F β) ≫
    nerveMap (leftCoefficientMap G' α))
  exact (rightCoefficientMap_isWeakHomotopyEquivalence F β hβ).comp
    (leftCoefficientMap_isWeakHomotopyEquivalence G' α hα)

end SerrePositivity.EInfinity.Hammock.TwoSidedGrothendieck
