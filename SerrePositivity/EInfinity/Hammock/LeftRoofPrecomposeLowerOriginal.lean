module

public import SerrePositivity.EInfinity.Hammock.LeftRoofPrecomposeLowerInsertion
public import SerrePositivity.EInfinity.Hammock.LeftRoofPrecomposeDiagram

/-!
# 始域比較の下行を元の前合成へ回収する全図式

概要：下行は元の始域射と roof の連結へ恒等列を挿入した同じ全図式。
方針：元の cut と連結の全縦射の回収を使う。
規約：元の射と全対象・全作用素を保持する。
使われ方：下行の nerve ホモトピーと元の前合成の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v uI vI
namespace SerrePositivity.EInfinity.Hammock.LeftRoof.Precompose
open CategoryTheory
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {I : Type uI} [Category.{vI} I] {X' X Y : C}
  (A : I ⥤ C) (p : A ⟶ (Functor.const I).obj X) (hp : ∀ i, W (p.app i))
  (f : X' ⟶ X) (σ : A ⟶ (Functor.const I).obj Y)
  (hA : ∀ {i j} (a : i ⟶ j), W (A.map a))

lemma lowerDiagram_insert :
    ((Functor.const I).obj (ForwardZigzag.obj (W := W) f)).prod'
        (LeftRoof.diagram W A p hp σ hA) ⋙
      ZigzagAppend.functor ⋙ WordAction.functor lowerInsert =
        lowerDiagram W A p hp f σ hA := by
  have ho (i : I) : WordAction.obj lowerInsert
      (ZigzagAppend.obj (ForwardZigzag.obj f) (LeftRoof.obj W (p.app i) (hp i) (σ.app i))) =
        lower W (p.app i) (hp i) f (σ.app i) := lowerInsert_obj W _ _ _ _
  apply CategoryTheory.Functor.hext ho
  intro i j a
  apply Zigzag.hom_hext (ho i) (ho j)
  intro k
  change HEq (ZigzagAppend.app (𝟙 (ForwardZigzag.obj (W := W) f))
    ((LeftRoof.diagram W A p hp σ hA).map a) (lowerInsert.cut k)) _
  rw [lowerInsert_cut]
  fin_cases k
  · exact ZigzagAppend.app_left_heq (𝟙 (ForwardZigzag.obj (W := W) f))
      ((LeftRoof.diagram W A p hp σ hA).map a) (0 : Fin 2)
  · exact ZigzagAppend.app_left_heq (𝟙 (ForwardZigzag.obj (W := W) f))
      ((LeftRoof.diagram W A p hp σ hA).map a) (0 : Fin 2)
  · exact ZigzagAppend.app_left_heq (𝟙 (ForwardZigzag.obj (W := W) f))
      ((LeftRoof.diagram W A p hp σ hA).map a) (1 : Fin 2)
  · exact ZigzagAppend.app_right_heq (𝟙 (ForwardZigzag.obj (W := W) f))
      ((LeftRoof.diagram W A p hp σ hA).map a) (1 : Fin 3)
  · exact ZigzagAppend.app_right_heq (𝟙 (ForwardZigzag.obj (W := W) f))
      ((LeftRoof.diagram W A p hp σ hA).map a) (2 : Fin 3)

end SerrePositivity.EInfinity.Hammock.LeftRoof.Precompose
