module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.WithTerminalOppositeNerveIso
public import SerrePositivity.InfinityCategories.F1B.Cones.CoconeExtension
public import SerrePositivity.InfinityCategories.Core.JoinTensorPoint

/-!
概要：元の終点付加余錐写像そのものを、join と nerve の同型として公開する。
方針：同じ余錐を反転し、始点 join の同型と圏の厳密な比較で可逆性を反映する。
規約：元の全余錐写像を選び直さず、元の両包含を保持する。
使われ方：有限半順序形状の下方部分を、厳密下方部分への余錐と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B
/-- 概要：既存の終点付加の全余錐写像は同型。
方針：余錐の反転公式。規約：元の全射を保持。使われ方：余錐形状の実同型。 -/
instance terminalJoinNerveMap_isIso (I : Type u) [Category.{u} I] :
    IsIso (terminalJoinNerveMap I) := by
  let c := withTerminalCocone I
  have hF : coneWithInitialFunctor c.op = (WithTerminal.opEquiv (C := I)).inverse := by
    apply CategoryTheory.Functor.ext
    · intro x y f
      cases x with
      | of x =>
        cases x
        cases y with
        | of y =>
          cases y
          simp only [eqToHom_refl, WithTerminal.opEquiv_inverse_map,
            Category.comp_id, Category.id_comp]
          exact Quiver.Hom.op_unop (WithInitial.down f)
        | star => exact PEmpty.elim f
      | star =>
        cases y with
        | of y => cases y; rfl
        | star => rfl
    · intro x
      cases x <;> rfl
  have hN : nerveMap (coneWithInitialFunctor c.op) =
      (withTerminalOppositeNerveIso I).inv := by rw [hF]; rfl
  have hr := nerveCocone_reverse_val c
  change (coconeReverseCone (nerveCoconeEquiv c)).val =
    joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveOppositeIso I).inv ≫
      (HomotopyLimits.initialJoinNerveIso Iᵒᵖ).hom ≫
      nerveMap (coneWithInitialFunctor c.op) ≫ (nerveOppositeIso (WithTerminal I)).hom at hr
  have hh : IsIso (coconeReverseCone (nerveCoconeEquiv c)).val := by
    rw [hr, hN]
    infer_instance
  rw [coconeReverseCone_val] at hh
  change IsIso (joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 (nerve I).op) ≫
    (stableJoinReverseIso (nerve I) Δ[0]).inv ≫
      SSet.opFunctor.map (terminalJoinNerveMap I)) at hh
  let := hh
  have h1 := IsIso.of_isIso_comp_left
    (joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 (nerve I).op))
    ((stableJoinReverseIso (nerve I) Δ[0]).inv ≫
      SSet.opFunctor.map (terminalJoinNerveMap I))
  let := h1
  have : IsIso (SSet.opFunctor.map (terminalJoinNerveMap I)) :=
    IsIso.of_isIso_comp_left (stableJoinReverseIso (nerve I) Δ[0]).inv _
  have hdouble : IsIso (SSet.opFunctor.map (SSet.opFunctor.map (terminalJoinNerveMap I))) :=
    inferInstance
  have he := (SSet.opFunctorCompOpFunctorIso).hom.naturality (terminalJoinNerveMap I)
  change SSet.opFunctor.map (SSet.opFunctor.map (terminalJoinNerveMap I)) ≫
    (SSet.opFunctorCompOpFunctorIso.app _).hom =
      (SSet.opFunctorCompOpFunctorIso.app _).hom ≫ terminalJoinNerveMap I at he
  exact IsIso.of_isIso_fac_left he.symm
/-- 概要：元の終点付加写像による join と nerve の同型。
方針：可逆性を束ねる。規約：順射は元の写像。使われ方：点追加の形状比較。 -/
def terminalJoinNerveIso (I : Type u) [Category.{u} I] :
    join (nerve I) (Δ[0] : SSet.{u}) ≅ nerve (WithTerminal I) :=
  asIso (terminalJoinNerveMap I)

/-- 概要：同型の順射は元の全余錐写像。
方針：定義を読む。規約：厳密な等号。使われ方：既存の余錐への接続。 -/
lemma terminalJoinNerveIso_hom (I : Type u) [Category.{u} I] :
    (terminalJoinNerveIso I).hom = terminalJoinNerveMap I := rfl
/-- 概要：元の圏側の包含を回収する。
方針：元の余錐の条件。規約：全射の等号。使われ方：点追加の共有境界。 -/
lemma joinInl_terminalJoinNerveIso (I : Type u) [Category.{u} I] :
    joinInl (nerve I) (Δ[0] : SSet.{u}) ≫ (terminalJoinNerveIso I).hom =
      nerveMap (WithTerminal.incl : I ⥤ WithTerminal I) :=
  (nerveCoconeEquiv (withTerminalCocone I)).property
/-- 概要：点側の包含を元の新しい終点へ戻す。
方針：元の余錐の頂点公式。規約：全射の等号。使われ方：点追加の指定終点。 -/
lemma joinInr_terminalJoinNerveIso (I : Type u) [Category.{u} I] :
    joinInr (nerve I) (Δ[0] : SSet.{u}) ≫ (terminalJoinNerveIso I).hom =
      nervePoint (WithTerminal.star : WithTerminal I) :=
  nerveCocone_point (withTerminalCocone I)

end SerrePositivity.InfinityCategories.F1B
