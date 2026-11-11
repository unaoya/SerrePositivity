module
public import SerrePositivity.KST.SConstruction.PointedSSetWhisker

/-! # 元の点つき全族の前後合成と標準豊穣自然性
概要：元の basedHom 族の可換式を、標準点つき豊穣の前後合成の可換式へ移す。
方針：同じ元の basedHom の前後合成を回収する公式を適用する。
規約：全パラメータの等号を入力とする。使われ方：巨大な dg 入力の包装の分割。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 元の全 basedHom 族の可換式は、標準点つき豊穣の同じ前後合成の可換式。 -/
lemma pointedFamily_whisker_naturality {P : SSet.{u}} (X Y Z W : PointedSSetObject.{u})
    (σ : X ⟶ Z) (τ : Y ⟶ W) (a : P ⟶ (X ⟶[SSet.{u}] Y))
    (b : P ⟶ (Z ⟶[SSet.{u}] W))
    (h : a ≫ pointedFamilyPost X.obj Y.obj W.obj τ =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre σ W.obj) :
    a ≫ eHomWhiskerLeft SSet X τ = b ≫ eHomWhiskerRight SSet σ W := by
  rw [pointedSSetObject_whiskerLeft, pointedSSetObject_whiskerRight]
  exact h

end SerrePositivity.KST.SConstruction
