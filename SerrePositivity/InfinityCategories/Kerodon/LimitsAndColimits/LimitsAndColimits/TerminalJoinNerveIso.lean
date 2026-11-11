module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.WithTerminalOppositeNerveIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint

/-!
概要：元の終点付加余錐写像そのものを、join と nerve の同型として公開する。
方針：同じ余錐を反転し、始点 join の同型と圏の厳密な比較で可逆性を反映する。
規約：元の全余錐写像を選び直さず、元の両包含を保持する。
使われ方：有限半順序形状の下方部分を、厳密下方部分への余錐と同定する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
/-- 概要：既存の終点付加の全余錐写像は同型。
方針：余錐の反転公式。規約：元の全射を保持。使われ方：余錐形状の実同型。 -/
instance terminalJoinNerveMap_isIso (I : Type u) [Category.{u} I] :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalJoinNerveMap I) := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.withTerminalCocone I
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c.op = (WithTerminal.opEquiv (C := I)).inverse := by
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
  have hN : nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c.op) =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.withTerminalOppositeNerveIso I).inv := by rw [hF]; rfl
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_reverse_val c
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c)).val =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOppositeIso I).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso Iᵒᵖ).hom ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c.op) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOppositeIso (WithTerminal I)).hom at hr
  have hh : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c)).val := by
    rw [hr, hN]
    infer_instance
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone_val] at hh
  change IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 (nerve I).op) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso (nerve I) Δ[0]).inv ≫
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalJoinNerveMap I)) at hh
  let := hh
  have h1 := IsIso.of_isIso_comp_left
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 (nerve I).op))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso (nerve I) Δ[0]).inv ≫
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalJoinNerveMap I))
  let := h1
  have : IsIso (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalJoinNerveMap I)) :=
    IsIso.of_isIso_comp_left (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso (nerve I) Δ[0]).inv _
  have hdouble : IsIso (SSet.opFunctor.map (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalJoinNerveMap I))) :=
    inferInstance
  have he := (SSet.opFunctorCompOpFunctorIso).hom.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalJoinNerveMap I)
  change SSet.opFunctor.map (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalJoinNerveMap I)) ≫
    (SSet.opFunctorCompOpFunctorIso.app _).hom =
      (SSet.opFunctorCompOpFunctorIso.app _).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalJoinNerveMap I at he
  exact IsIso.of_isIso_fac_left he.symm
/-- 概要：元の終点付加写像による join と nerve の同型。
方針：可逆性を束ねる。規約：順射は元の写像。使われ方：点追加の形状比較。 -/
def terminalJoinNerveIso (I : Type u) [Category.{u} I] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (nerve I) (Δ[0] : SSet.{u}) ≅ nerve (WithTerminal I) :=
  asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalJoinNerveMap I)

/-- 概要：同型の順射は元の全余錐写像。
方針：定義を読む。規約：厳密な等号。使われ方：既存の余錐への接続。 -/
lemma terminalJoinNerveIso_hom (I : Type u) [Category.{u} I] :
    (terminalJoinNerveIso I).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalJoinNerveMap I := rfl
/-- 概要：元の圏側の包含を回収する。
方針：元の余錐の条件。規約：全射の等号。使われ方：点追加の共有境界。 -/
lemma joinInl_terminalJoinNerveIso (I : Type u) [Category.{u} I] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (nerve I) (Δ[0] : SSet.{u}) ≫ (terminalJoinNerveIso I).hom =
      nerveMap (WithTerminal.incl : I ⥤ WithTerminal I) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.withTerminalCocone I)).property
/-- 概要：点側の包含を元の新しい終点へ戻す。
方針：元の余錐の頂点公式。規約：全射の等号。使われ方：点追加の指定終点。 -/
lemma joinInr_terminalJoinNerveIso (I : Type u) [Category.{u} I] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (nerve I) (Δ[0] : SSet.{u}) ≫ (terminalJoinNerveIso I).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (WithTerminal.star : WithTerminal I) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_point (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.withTerminalCocone I)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
