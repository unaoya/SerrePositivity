module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCylinder

/-!
概要：標準区間から可逆な区間への単射。
方針：零・一頂点を Bool の false・true へ写す。
規約：単体の全頂点で単射性を検出する。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆な円柱による同型の表示。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：標準区間の二頂点を可逆な区間の異なる二頂点へ写す。
方針：頂点の割当てを codiscrete nerve への射に延長する。
規約：0 は false、1 は true。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆区間の中の標準区間。 -/
def equivalenceIntervalEdge : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap (fun x ↦ ULift.up (decide (x 0 = 1)))

/-- 概要：可逆区間への標準区間の包含は単射。
方針：各単体の各頂点を Bool に戻して元の頂点値を復元する。
規約：全ての次数で単射。
使われ方：Kerodon §4.5.3（Tag 032Y） の trivial Kan fibration への持ち上げ。 -/
instance equivalenceIntervalEdge_mono : Mono equivalenceIntervalEdge.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  apply (mono_iff_injective _).2
  intro s t h
  apply stdSimplex.ext
  intro i
  have hi := congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval.{u} _⦋n⦌ ↦ ((z.obj i).as).down) h
  change decide (s i = 1) = decide (t i = 1) at hi
  have hh : (s i = 1) ↔ (t i = 1) := decide_eq_decide.mp hi
  omega

/-- 概要：標準区間の零端は可逆区間の false 端へ写る。
方針：全ての対象の値を比較する。
規約：始域は標準零単体。
使われ方：Kerodon §4.5.3（Tag 032Y） の円柱の端点。 -/
lemma equivalenceIntervalEdge_zero :
    stdSimplex.δ (1 : Fin 2) ≫ equivalenceIntervalEdge.{u} =
      SSet.const (nerveEquiv.symm (Codiscrete.mk (ULift.up false))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerve_hom_ext
  intro x
  have hx : x 0 = 0 := by omega
  change ULift.up (decide ((Fin.succAbove (1 : Fin 2) (x 0)) = 1)) = _
  simp [hx]

/-- 概要：標準区間の一端は可逆区間の true 端へ写る。
方針：全ての対象の値を比較する。
規約：始域は標準零単体。
使われ方：Kerodon §4.5.3（Tag 032Y） の円柱の端点。 -/
lemma equivalenceIntervalEdge_one :
    stdSimplex.δ (0 : Fin 2) ≫ equivalenceIntervalEdge.{u} =
      SSet.const (nerveEquiv.symm (Codiscrete.mk (ULift.up true))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerve_hom_ext
  intro x
  have hx : x 0 = 0 := by omega
  change ULift.up (decide ((Fin.succAbove (0 : Fin 2) (x 0)) = 1)) = _
  simp [hx]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
