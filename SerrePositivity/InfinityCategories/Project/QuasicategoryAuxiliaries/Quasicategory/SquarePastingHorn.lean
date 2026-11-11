module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathInnerFibration
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PastingShapes
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：共有辺が一致する二つの正方形を、内ホーン上の矢印族として貼る。
方針：転置した正方形を curry して、二次内ホーンの押し出しを使う。
規約：両正方形と四つの水平辺を厳密に保持。使われ方：指定合成を持つ長方形の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn
end SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn
variable {X : SSet.{u}} (L R : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ L = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ R)

def transposed (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  curry ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ S)

include h in
lemma compatible : stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed L =
    stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed R := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed,
    uncurry_curry, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  have ht : t = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n := by
    apply SSet.stdSimplex.ext
    intro j
    apply Fin.ext
    have ht := (t j).isLt
    have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n j).isLt
    omega
  subst t
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋n⦌)) s
  exact he

def diagram : (horn 2 1 : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  horn₂₁.isPushout.desc (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed L) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed R) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.compatible L R h)

lemma diagram_left : horn₂₁.ι₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.diagram L R h = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed L :=
  horn₂₁.isPushout.inl_desc _ _ _

lemma diagram_right : horn₂₁.ι₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.diagram L R h = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed R :=
  horn₂₁.isPushout.inr_desc _ _ _

lemma transposed_bottom (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed S ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ S := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
  rfl

lemma transposed_top (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed S ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ S := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
  rfl

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn.compatible := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.compatible

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.diagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn.diagram := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.diagram

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn.diagram_left := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.diagram_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn.diagram_right := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.diagram_right

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn.transposed := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn.transposed_bottom := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn.transposed_top := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed_top

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn.diagram._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.diagram._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn.diagram._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.diagram._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn.transposed.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.transposed.eq_1
