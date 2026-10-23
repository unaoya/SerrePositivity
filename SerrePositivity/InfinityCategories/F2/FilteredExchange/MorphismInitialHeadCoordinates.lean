module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.MorphismInitialTailHead
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.InitialReverseThickeningCoordinates

/-!
概要：元の初点取り替え単体の head を、元の二時刻の指定表示で計算する。
方針：標的だけを移送し、元の tail の恒等射・指定射の式を適用する。
規約：元の全 Hom 係数を保つ。使われ方：反転合成 prism との実 Hom の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の初点 Hom の標的だけの表示変更は、元の tail の同じ表示変更に一致する。 -/
lemma coneInitialHead_transport_target (x : C) {n : ℕ}
    (T : (SimplicialNerve C) _⦋n + 1⦌)
    (p : Δ[n] ⟶ (SimplicialCategory.sHom x (T.obj ⟨ULift.up 0⟩)).op)
    (j : Fin (n + 1)) {Z : C} (h : T.obj ⟨ULift.up j.succ⟩ = Z) :
    coneInitialHead x T p j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom rfl h) =
      lift (pathFirstParameterMap j ≫ reflectedSimplexMap p)
        (T.map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ ≫
          eqToHom (congrArg₂ SimplicialCategory.sHom rfl h)) ≫
        eComp SSet x (T.obj ⟨ULift.up 0⟩) Z := by
  subst Z
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- 元の零時刻の head は同じ元の初点係数の評価。 -/
lemma morphismInitialHead_zero {X Y : C} (f : X ⟶ Y) (x : C) {n : ℕ}
    (α : ⦋n⦌ ⟶ ⦋1⦌) (p : (SimplicialCategory.sHom x X).op _⦋n⦌)
    (j : Fin (n + 1)) (hj : α.toOrderHom j = 0) :
    coneInitialHead x (morphismInitialTail f α).val (SSet.yonedaEquiv.symm p) j ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom rfl
        (morphismInitialTail_obj_zero f α j hj)) =
      pathFirstParameterMap j ≫ reflectedSimplexMap (SSet.yonedaEquiv.symm p) := by
  rw [coneInitialHead_transport_target x (morphismInitialTail f α).val
    (SSet.yonedaEquiv.symm p) j (morphismInitialTail_obj_zero f α j hj),
    morphismInitialTail_head_zero f α j hj]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  exact simplicialHom_comp_id_app x X d _

/-- 元の一時刻の head は、同じ元の初点係数に続く元の指定射の合成。 -/
lemma morphismInitialHead_one {X Y : C} (f : X ⟶ Y) (x : C) {n : ℕ}
    (α : ⦋n⦌ ⟶ ⦋1⦌) (p : (SimplicialCategory.sHom x X).op _⦋n⦌)
    (j : Fin (n + 1)) (hj : α.toOrderHom j = 1) :
    coneInitialHead x (morphismInitialTail f α).val (SSet.yonedaEquiv.symm p) j ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom rfl
        (morphismInitialTail_obj_one f α j hj)) =
      lift (pathFirstParameterMap j ≫ reflectedSimplexMap (SSet.yonedaEquiv.symm p))
        (SSet.const (SimplicialCategory.homEquiv' X Y f)) ≫ eComp SSet x X Y := by
  rw [coneInitialHead_transport_target x (morphismInitialTail f α).val
    (SSet.yonedaEquiv.symm p) j (morphismInitialTail_obj_one f α j hj),
    morphismInitialTail_head_one f α j hj]
  rfl

end SerrePositivity.InfinityCategories.F2
