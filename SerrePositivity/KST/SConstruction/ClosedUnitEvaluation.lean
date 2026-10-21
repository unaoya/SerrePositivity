module
public import SerrePositivity.KST.SConstruction.SOneComparison
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedActionLaws

/-! # 単位内部 Hom の元の評価と全族合成
概要：単位からの内部 Hom の標準同型を評価式で回収し、全族の合成との可換性を示す。
方針：随伴の mate の counit 式と、同じ内部 Hom 合成の各単体の評価を使う。
規約：通常の自然性だけに制限しない。使われ方：元の S₁ 比較の全族自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- 単位内部 Hom の標準逆同型は、同じ単位の元での評価である。 -/
lemma closedUnitIso_inv (X : SSet.{u}) :
    (MonoidalClosed.unitNatIso (C := SSet.{u})).inv.app X =
      (λ_ ((ihom (𝟙_ SSet.{u})).obj X)).inv ≫ (ihom.ev (𝟙_ SSet.{u})).app X := by
  have h := conjugateEquiv_counit (ihom.adjunction (𝟙_ SSet.{u}))
    (Adjunction.id (C := SSet.{u})) (leftUnitorNatIso SSet.{u}).inv X
  change (MonoidalClosed.unitNatIso (C := SSet.{u})).inv.app X ≫ 𝟙 X =
    (λ_ ((ihom (𝟙_ SSet.{u})).obj X)).inv ≫ (ihom.ev (𝟙_ SSet.{u})).app X at h
  exact (Category.comp_id _).symm.trans h

/-- 単位での評価は、全内部 Hom 族による後合成と厳密に可換する。 -/
lemma closedUnitIso_inv_comp (X Y : SSet.{u}) :
    MonoidalClosed.comp (𝟙_ SSet.{u}) X Y ≫
      (MonoidalClosed.unitNatIso (C := SSet.{u})).inv.app Y =
    ((MonoidalClosed.unitNatIso (C := SSet.{u})).inv.app X ⊗ₘ
      𝟙 ((ihom X).obj Y)) ≫ (ihom.ev X).app Y := by
  rw [closedUnitIso_inv, closedUnitIso_inv]
  ext n z
  rfl

/-- 固定した添字の前合成は、全内部 Hom 族の後合成と厳密に可換する。 -/
lemma closedComp_pre {A B : SSet.{u}} (e : B ⟶ A) (X Y : SSet.{u}) :
    MonoidalClosed.comp A X Y ≫ (pre e).app Y =
      ((pre e).app X ⊗ₘ 𝟙 ((ihom X).obj Y)) ≫ MonoidalClosed.comp B X Y := by
  ext n z
  apply Functor.functorHom_ext
  intro m f
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 固定した単位からの添字での評価は、全 Hom 族の後合成と厳密に可換する。 -/
lemma closedEvaluationAlong_comp {A : SSet.{u}} (e : 𝟙_ SSet.{u} ⟶ A) (X Y : SSet.{u}) :
    MonoidalClosed.comp A X Y ≫ (pre e).app Y ≫
      (MonoidalClosed.unitNatIso (C := SSet.{u})).inv.app Y =
    (((pre e).app X ≫ (MonoidalClosed.unitNatIso (C := SSet.{u})).inv.app X) ⊗ₘ
      𝟙 ((ihom X).obj Y)) ≫ (ihom.ev X).app Y := by
  rw [← Category.assoc, closedComp_pre, Category.assoc, closedUnitIso_inv_comp,
    ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

/-- 部分図式と全入力族を合成する前後で、同じ固定添字への評価が一致する。 -/
lemma closedEvaluationFamily_action {A X Y S P : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ A) (j : S ⟶ (ihom A).obj X) (p : P ⟶ (ihom X).obj Y) :
    ((j ≫ (pre e).app X ≫ (MonoidalClosed.unitNatIso (C := SSet.{u})).inv.app X) ▷ P) ≫
        uncurry p =
    (j ⊗ₘ p) ≫ MonoidalClosed.comp A X Y ≫ (pre e).app Y ≫
      (MonoidalClosed.unitNatIso (C := SSet.{u})).inv.app Y := by
  ext n z
  have h := types_congr_hom (NatTrans.congr_app (closedEvaluationAlong_comp e X Y) n)
    (j.app n z.1, p.app n z.2)
  exact h.symm

end SerrePositivity.KST.SConstruction
