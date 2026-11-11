module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd

/-!
概要：四辺と四つの端点の一致から、正方形の境界上の全図式を構成する。
方針：二方向の区間境界の積の和で貼り合わせる。
規約：境界の内部に二単体を加えない。使われ方：四辺を同時に固定した正方形の変形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.SquareFrame
end SerrePositivity.KST.LocalizingInvariants.SquareFrame
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

@[ext] structure SquareFrame (X : SSet.{u}) where
  bottom : (Δ[1] : SSet.{u}) ⟶ X
  top : (Δ[1] : SSet.{u}) ⟶ X
  left : (Δ[1] : SSet.{u}) ⟶ X
  right : (Δ[1] : SSet.{u}) ⟶ X
  lower_left : stdSimplex.δ (1 : Fin 2) ≫ bottom = stdSimplex.δ (1 : Fin 2) ≫ left
  lower_right : stdSimplex.δ (0 : Fin 2) ≫ bottom = stdSimplex.δ (1 : Fin 2) ≫ right
  upper_left : stdSimplex.δ (1 : Fin 2) ≫ top = stdSimplex.δ (0 : Fin 2) ≫ left
  upper_right : stdSimplex.δ (0 : Fin 2) ≫ top = stdSimplex.δ (0 : Fin 2) ≫ right

namespace SquareFrame

variable {X : SSet.{u}} (f : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame X)

abbrev boundary : SSet.{u} := Subcomplex.unionProd (SSet.boundary 1)
  (SSet.boundary 1)

def boundaryι : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundary.{u} ⟶ (Δ[1] ⊗ Δ[1] : SSet.{u}) :=
  (Subcomplex.unionProd (SSet.boundary 1) (SSet.boundary 1)).ι

instance instMonoSSetBoundaryι : Mono _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι.{u} := inferInstanceAs
  (Mono (Subcomplex.unionProd (SSet.boundary 1) (SSet.boundary 1)).ι)

def horizontal : (Δ[1] : SSet.{u}) ⊗ (SSet.boundary 1 : SSet.{u}) ⟶ X :=
  (β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f.bottom f.top

def vertical : (SSet.boundary 1 : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f.left f.right

lemma compatible : ((SSet.boundary 1).ι ▷ (SSet.boundary 1 : SSet.{u})) ≫ f.horizontal =
    ((SSet.boundary 1 : SSet.{u}) ◁ (SSet.boundary 1).ι) ≫ f.vertical := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  let c : (Δ[0] : SSet.{u}) _⦋n⦌ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n
  have hv (v : (SSet.boundary 1 : SSet.{u}) _⦋n⦌) (i : Fin 2) (hi : v.val 0 = i) :
      v.val = (stdSimplex.δ (if i = 0 then 1 else 0 : Fin 2)).app (Opposite.op ⦋n⦌) c := by
    apply SSet.stdSimplex.ext
    intro j
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.boundaryOne_simplex_constant v j, hi]
    fin_cases i <;> rfl
  change (if t.val 0 = 0 then f.bottom.app _ s.val else f.top.app _ s.val) =
    (if s.val 0 = 0 then f.left.app _ t.val else f.right.app _ t.val)
  generalize hi : s.val 0 = i
  generalize hj : t.val 0 = j
  fin_cases i <;> fin_cases j
  · simpa [hv s 0 hi, hv t 0 hj] using
      ConcreteCategory.congr_hom (NatTrans.congr_app f.lower_left (Opposite.op ⦋n⦌)) c
  · simpa [hv s 0 hi, hv t 1 hj] using
      ConcreteCategory.congr_hom (NatTrans.congr_app f.upper_left (Opposite.op ⦋n⦌)) c
  · simpa [hv s 1 hi, hv t 0 hj] using
      ConcreteCategory.congr_hom (NatTrans.congr_app f.lower_right (Opposite.op ⦋n⦌)) c
  · simpa [hv s 1 hi, hv t 1 hj] using
      ConcreteCategory.congr_hom (NatTrans.congr_app f.upper_right (Opposite.op ⦋n⦌)) c

def diagram : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundary.{u} ⟶ X :=
  (Subcomplex.unionProd.isPushout (SSet.boundary 1) (SSet.boundary 1)).desc
    f.horizontal f.vertical f.compatible

lemma diagram_horizontal : Subcomplex.unionProd.ι₁ (SSet.boundary 1) (SSet.boundary 1) ≫
    f.diagram = f.horizontal := (Subcomplex.unionProd.isPushout _ _).inl_desc _ _ _

lemma diagram_vertical : Subcomplex.unionProd.ι₂ (SSet.boundary 1) (SSet.boundary 1) ≫
    f.diagram = f.vertical := (Subcomplex.unionProd.isPushout _ _).inr_desc _ _ _

end SquareFrame
end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.bottom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.bottom := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.bottom

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundary (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.boundary := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundary

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.boundaryι := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.casesOn := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.casesOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.compatible := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.compatible

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.diagram := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.diagram_horizontal := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram_horizontal

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.diagram_vertical := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram_vertical

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.ext := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.ext

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.ext_iff := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.ext_iff

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.horizontal (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.horizontal := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.horizontal

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.instMonoSSetBoundaryι (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.instMonoSSetBoundaryι := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.instMonoSSetBoundaryι

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.left (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.left := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.lower_left := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.lower_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.lower_right := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.lower_right

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.mk := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.rec := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.recOn := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.right (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.right := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.right

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.top (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.top := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.top

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.upper_left := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.upper_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.upper_right := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.upper_right

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.vertical (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.vertical := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.vertical

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.diagram._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.diagram._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.mk.sizeOf_spec
