module

public import SerrePositivity.EInfinity.Hammock.ThreeArrow
public import SerrePositivity.EInfinity.Hammock.DirectionArrowComparison
public import SerrePositivity.EInfinity.Hammock.UniverseValue
public import SerrePositivity.EInfinity.FrameHom.SpecialSpanLocalization
public import SerrePositivity.EInfinity.FrameHom.SpecialThreeArrowComparison

/-!
# 元の三本矢と全語の hammock の評価の一致

概要：同じ左脚・中間射・右脚から得る元の局所化射を回収する。
方針：元の三列の評価を展開し、同じ二つの逆射を照合する。
規約：特殊な三本矢も元の包含を通して評価する。
使われ方：既存 Map^h の高次比較と π₀ の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.ThreeArrow
open CategoryTheory HomotopicalAlgebra SerrePositivity.EInfinity.FrameHom
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

lemma special_value (S : SpecialHammock X Y) :
    Zigzag.Value.value (weakEquivalences C).Q (weakEquivalences C).Q_inverts
        (obj ((WeakThreeArrow.inclusion X Y).obj S)) = SpecialHammock.value S := by
  let Q := (weakEquivalences C).Q
  have : IsIso (Q.map S.leftMap) := Localization.inverts Q _ _ S.left_mem.2
  have : IsIso (Q.map S.rightMap) := Localization.inverts Q _ _ S.right_mem.2
  dsimp only [Zigzag.Value.value]
  simp only [obj, eqToHom_refl, Category.id_comp, Category.comp_id]
  change (Zigzag.Value.path Q (weakEquivalences C).Q_inverts
    (obj ((WeakThreeArrow.inclusion X Y).obj S))).map' 0 3 = _
  rw [ComposableArrows.map'_comp _ 0 1 3, ComposableArrows.map'_comp _ 1 2 3]
  simp only [Zigzag.Value.path, ComposableArrows.mkOfObjOfMapSucc_map_succ]
  change Zigzag.Value.edge Q (weakEquivalences C).Q_inverts
      (obj ((WeakThreeArrow.inclusion X Y).obj S)) (0 : Fin 3) ≫
    Zigzag.Value.edge Q (weakEquivalences C).Q_inverts
      (obj ((WeakThreeArrow.inclusion X Y).obj S)) (1 : Fin 3) ≫
    Zigzag.Value.edge Q (weakEquivalences C).Q_inverts
      (obj ((WeakThreeArrow.inclusion X Y).obj S)) (2 : Fin 3) = _
  let z := obj ((WeakThreeArrow.inclusion X Y).obj S)
  have hb0 : (Direction.arrow .backward z (0 : Fin 3) rfl).unop = S.leftMap :=
    congrArg Quiver.Hom.unop (eq_of_heq (Direction.backward_arrow_heq z (0 : Fin 3) rfl))
  have hb2 : (Direction.arrow .backward z (2 : Fin 3) rfl).unop = S.rightMap :=
    congrArg Quiver.Hom.unop (eq_of_heq (Direction.backward_arrow_heq z (2 : Fin 3) rfl))
  have hf1 : Direction.arrow .forward z (1 : Fin 3) rfl = S.middle :=
    eq_of_heq (Direction.forward_arrow_heq z (1 : Fin 3) rfl)
  have h0 : Zigzag.Value.edge Q (weakEquivalences C).Q_inverts z (0 : Fin 3) =
      inv (Q.map S.leftMap) := by
    simpa only [Zigzag.Value.backwardIso, asIso_inv, hb0] using
      (Zigzag.Value.edge_backward Q (weakEquivalences C).Q_inverts z (0 : Fin 3) rfl)
  have h1 : Zigzag.Value.edge Q (weakEquivalences C).Q_inverts z (1 : Fin 3) =
      Q.map S.middle :=
    (Zigzag.Value.edge_forward Q (weakEquivalences C).Q_inverts z (1 : Fin 3) rfl).trans
      (congrArg Q.map hf1)
  have h2 : Zigzag.Value.edge Q (weakEquivalences C).Q_inverts z (2 : Fin 3) =
      inv (Q.map S.rightMap) := by
    simpa only [Zigzag.Value.backwardIso, asIso_inv, hb2] using
      (Zigzag.Value.edge_backward Q (weakEquivalences C).Q_inverts z (2 : Fin 3) rfl)
  exact congrArg₂ (fun f g => f ≫ g) h0 (congrArg₂ (fun f g => f ≫ g) h1 h2)

end SerrePositivity.EInfinity.Hammock.ThreeArrow
