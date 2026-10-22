module
public import SerrePositivity.KST.SConstruction.CoaugmentedClosedFamily

/-! # 同じ monoidal 比較と単位による tensor strength
概要：元のパラメータを単位で写す前向き比較と、全パラメータ作用との結合則を与える。
方針：全単体で元の乗法比較の結合律・自然性を評価する。
規約：頂点だけに制限しない。使われ方：suspension 比較の全入力族自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Functor.LaxMonoidal
variable (F : SSet.{u} ⥤ SSet.{u}) [F.LaxMonoidal]
  (η : 𝟭 SSet.{u} ⟶ F)

/-- 左の元のパラメータだけを単位で写す、同じ乗法比較。 -/
def coaugmentedTensorLeftStrength (K X : SSet.{u}) : K ⊗ F.obj X ⟶ F.obj (K ⊗ X) :=
  (η.app K ▷ F.obj X) ≫ μ F K X

/-- 右の元のパラメータだけを単位で写す、同じ乗法比較。 -/
def coaugmentedTensorRightStrength (X P : SSet.{u}) : F.obj X ⊗ P ⟶ F.obj (X ⊗ P) :=
  (F.obj X ◁ η.app P) ≫ μ F X P

/-- 元の左右のパラメータは、同じ三重 tensor 上で乗法比較の結合律を保つ。 -/
lemma coaugmentedTensorStrength_associativity (K X P : SSet.{u}) :
    (α_ K (F.obj X) P).hom ≫
      (K ◁ coaugmentedTensorRightStrength F η X P) ≫
      coaugmentedTensorLeftStrength F η K (X ⊗ P) =
    (coaugmentedTensorLeftStrength F η K X ▷ P) ≫
      coaugmentedTensorRightStrength F η (K ⊗ X) P ≫ F.map (α_ K X P).hom := by
  ext n t
  exact (types_congr_hom (NatTrans.congr_app (associativity F K X P) n)
    (((η.app K).app n t.1.1, t.1.2), (η.app P).app n t.2)).symm

/-- 任意の全パラメータ作用は、元の左 strength と厳密に可換する。 -/
lemma coaugmentedTensorStrength_action {K X Y P : SSet.{u}} (a : X ⊗ P ⟶ Y) :
    (α_ K (F.obj X) P).hom ≫
      (K ◁ (coaugmentedTensorRightStrength F η X P ≫ F.map a)) ≫
      coaugmentedTensorLeftStrength F η K Y =
    (coaugmentedTensorLeftStrength F η K X ▷ P) ≫
      coaugmentedTensorRightStrength F η (K ⊗ X) P ≫
      F.map ((α_ K X P).hom ≫ (K ◁ a)) := by
  ext n t
  have hn := types_congr_hom (NatTrans.congr_app (μ_natural_right F K a) n)
    ((η.app K).app n t.1.1,
      (μ F X P).app n (t.1.2, (η.app P).app n t.2))
  have ha := types_congr_hom (NatTrans.congr_app (associativity F K X P) n)
    (((η.app K).app n t.1.1, t.1.2), (η.app P).app n t.2)
  have hc := types_congr_hom (NatTrans.congr_app (F.map_comp (α_ K X P).hom (K ◁ a)) n)
    ((μ F (K ⊗ X) P).app n
      ((μ F K X).app n ((η.app K).app n t.1.1, t.1.2), (η.app P).app n t.2))
  exact hn.trans ((congrArg (fun z => (F.map (K ◁ a)).app n z) ha.symm).trans hc.symm)

/-- 全閉 Hom 作用は、右 strength の後の同じ元の族の像として回収される。 -/
lemma coaugmentedClosedFamilyMap_strength {X Y P : SSet.{u}}
    (a : P ⟶ (ihom X).obj Y) :
    uncurry (a ≫ coaugmentedClosedFamilyMap F η X Y) =
      coaugmentedTensorRightStrength F η X P ≫ F.map (uncurry a) := by
  have hn : a ≫ η.app ((ihom X).obj Y) = η.app P ≫ F.map a := η.naturality a
  rw [coaugmentedClosedFamilyMap, ← Category.assoc, hn,
    Category.assoc, uncurry_natural_left, laxClosedFamilyMap,
    uncurry_natural_left, uncurry_curry]
  rw [μ_natural_right_assoc, ← F.map_comp]
  rfl

end SerrePositivity.KST.SConstruction
