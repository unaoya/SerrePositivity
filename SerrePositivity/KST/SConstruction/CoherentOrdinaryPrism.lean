module
public import SerrePositivity.KST.SConstruction.CoherentArrowNativeFamilies

/-! # 通常圏の nerve と区間の積の厳密な通常圏表示
概要：元の全入力 prism を、通常圏と二点順序圏の積の nerve と厳密に同定する。
方針：各合成列を第一射影と時刻の順序写像へ分け、元の対の列へ戻す。
規約：入力と Hom の宇宙を保ち、元の区間と全合成列を置き換えない。
使われ方：元の K prism に全合成列の native Hom 評価を直接適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 積圏の全合成列を、元の入力列と元の時刻単体へ分ける。 -/
def coherentOrdinaryPrismForward (I : Type u) [SmallCategory I] :
    (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) ⟶
      (SSet.uliftFunctor.{v, u}).obj (nerve I) ⊗ (Δ[1] : SSet.{max u v}) where
  app n := ↾fun s =>
    (ULift.up (s.down ⋙ CategoryTheory.Prod.fst I (ULift.{u} (Fin 2))),
      SSet.stdSimplex.objEquiv.symm (SimplexCategory.mkHom
        ⟨fun i => (s.down.obj i).2.down, fun i j hij =>
          (s.down.map (homOfLE hij)).2.le⟩))
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro i
      rfl

/-- 元の入力列と元の時刻単体から、同じ積圏の全合成列を戻す。 -/
def coherentOrdinaryPrismBackward (I : Type u) [SmallCategory I] :
    (SSet.uliftFunctor.{v, u}).obj (nerve I) ⊗ (Δ[1] : SSet.{max u v}) ⟶
      (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) where
  app n := ↾fun s => ULift.up (s.1.down.prod'
    (s.2.down.toOrderHom.monotone.functor ⋙
      (ULift.orderIso : ULift.{u} (Fin 2) ≃o Fin 2).symm.monotone.functor))
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro s
    rfl

/-- 積圏の全合成列は、分割と復元で全次数において厳密に回収する。 -/
lemma coherentOrdinaryPrism_forward_backward (I : Type u) [SmallCategory I] :
    coherentOrdinaryPrismForward.{u, v} I ≫ coherentOrdinaryPrismBackward I = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j a
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim _ _

/-- 元の入力列と時刻単体も、復元と分割で厳密に回収する。 -/
lemma coherentOrdinaryPrism_backward_forward (I : Type u) [SmallCategory I] :
    coherentOrdinaryPrismBackward.{u, v} I ≫ coherentOrdinaryPrismForward I = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · apply ULift.ext
    exact CategoryTheory.Functor.ext (fun _ => rfl)
  · apply SSet.stdSimplex.ext
    intro i
    rfl

/-- 元の prism の始域を、同じ通常積圏の nerve で表示する厳密な同型。 -/
def coherentOrdinaryPrismIso (I : Type u) [SmallCategory I] :
    (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) ≅
      (SSet.uliftFunctor.{v, u}).obj (nerve I) ⊗ (Δ[1] : SSet.{max u v}) where
  hom := coherentOrdinaryPrismForward I
  inv := coherentOrdinaryPrismBackward I
  hom_inv_id := coherentOrdinaryPrism_forward_backward I
  inv_hom_id := coherentOrdinaryPrism_backward_forward I

end SerrePositivity.KST.SConstruction
