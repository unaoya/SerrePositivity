module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse

/-!
概要：三つの区間 x→a、x→y、y→b から a→b を、元の二つの合成三角形を保って構成する。
方針：Kan 亜群で辺を選び、合成等式を実三角形へ戻す。射影後も同じ三角形を使う。
規約：区間の類の式だけでなく二単体を保持。使われ方：調整した構造比較の境界トレース。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.ThreeEdgeTransport
end SerrePositivity.KST.Spectra.ThreeEdgeTransport
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra

/-- 二つの三角形を保持した、左端を逆向きに通る三辺の輸送。 -/
structure ThreeEdgeTransport {Z : SSet.{u}} {x a y b : Z _⦋0⦌}
    (left : Z.Edge x a) (middle : Z.Edge x y) (right : Z.Edge y b) where
  diagonal : Z.Edge x b
  transported : Z.Edge a b
  first : SSet.Edge.CompStruct middle right diagonal
  second : SSet.Edge.CompStruct left transported diagonal

namespace ThreeEdgeTransport

variable {Z : SSet.{u}} {x a y b : Z _⦋0⦌}
  (left : Z.Edge x a) (middle : Z.Edge x y) (right : Z.Edge y b)

/-- Kan 充填により二つの三角形を持つ輸送辺を構成する。 -/
def choose [KanComplex Z] : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport left middle right := by
  let leftIso : IsIso (SSet.Truncated.HomotopyCategory.homMk left.toTruncated) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers left.toTruncated
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex left.toTruncated)
  let d := middle.toTruncated.comp right.toTruncated
  let hex := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective a b
    (inv (SSet.Truncated.HomotopyCategory.homMk left.toTruncated) ≫
      SSet.Truncated.HomotopyCategory.homMk d)
  let e := hex.choose
  have he := hex.choose_spec
  have hf : SSet.Truncated.HomotopyCategory.homMk left.toTruncated ≫
      SSet.Truncated.HomotopyCategory.homMk e =
        SSet.Truncated.HomotopyCategory.homMk d := by
    rw [he, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  exact ⟨SSet.Edge.ofTruncated d, SSet.Edge.ofTruncated e,
    SSet.Edge.CompStruct.ofTruncated (middle.toTruncated.compStruct right.toTruncated),
    SSet.Edge.CompStruct.ofTruncated (Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hf))⟩

variable {left middle right}

/-- 保持した二つの実三角形による、元の辺の類の厳密な合成式。 -/
lemma trace (D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport left middle right) :
    SSet.HomotopyCategory.homMk left ≫ SSet.HomotopyCategory.homMk D.transported =
      SSet.HomotopyCategory.homMk middle ≫ SSet.HomotopyCategory.homMk right :=
  (SSet.HomotopyCategory.homMk_comp_homMk D.second).trans
    (SSet.HomotopyCategory.homMk_comp_homMk D.first).symm

/-- 輸送後の辺だけを選び直さず、二つの三角形全体を同じ射で写す。 -/
def map {W : SSet.{u}} (D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport left middle right) (p : Z ⟶ W) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport (left.map p) (middle.map p) (right.map p) where
  diagonal := D.diagonal.map p
  transported := D.transported.map p
  first := D.first.map p
  second := D.second.map p

/-- 射影後のトレースも、元の三つの区間と同じ二つの三角形で計算する。 -/
lemma map_trace {W : SSet.{u}} (D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport left middle right) (p : Z ⟶ W) :
    SSet.HomotopyCategory.homMk (left.map p) ≫
        SSet.HomotopyCategory.homMk (D.transported.map p) =
      SSet.HomotopyCategory.homMk (middle.map p) ≫
        SSet.HomotopyCategory.homMk (right.map p) :=
  (D.map p).trace

end ThreeEdgeTransport
end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.casesOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.choose (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.choose := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.choose

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.diagonal (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.diagonal := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.diagonal

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.first (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.first := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.first

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.map (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.map := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.map_trace := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.map_trace

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.mk := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.rec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.recOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.second (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.second := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.second

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.trace := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.trace

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.transported (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.transported := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.transported

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.choose._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.choose._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.choose._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.choose._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.choose._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.choose._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.choose._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.choose._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.choose._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.choose._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.choose._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.choose._proof_6

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.mk.sizeOf_spec
