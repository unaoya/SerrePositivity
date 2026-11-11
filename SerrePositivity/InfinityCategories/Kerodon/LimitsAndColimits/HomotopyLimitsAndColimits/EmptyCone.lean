module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap

/-!
概要：空図式の極限錐を終対象の頂点と同定する。
方針：空図式上の slice の射影が厳密な同型であることを示す。
規約：空図式は標的の空部分複体の包含として表す。
使われ方：HTT 1.2.13、4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の空積。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：指定した頂点を頂点とする空図式上の錐。
方針：空因子との join の単位同型を零単体の射に合成する。
規約：空図式は X の空部分複体の包含。
使われ方：Kerodon 7.1（Tag 02H1）、7.5.4.6（Tag 03BB） の空積の具体的な錐。 -/
noncomputable def emptyCone {X : SSet.{u}} (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (⊥ : X.Subcomplex).ι :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso Δ[0] X).hom ≫ SSet.yonedaEquiv.symm x,
    Subcomplex.isInitialBot.hom_ext _ _⟩

/-- 概要：空図式の錐の頂点は指定した頂点に一致する。
方針：join の単位同型の逆射が左包含であることを使う。
規約：頂点の命題的な等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の空積の対象との照合。 -/
lemma emptyCone_vertex {X : SSet.{u}} (x : X _⦋0⦌) : (emptyCone x).vertex = x := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] ((⊥ : X.Subcomplex) : SSet.{u}) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso Δ[0] X).hom ≫ SSet.yonedaEquiv.symm x)) = x
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso_inv, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- 概要：空図式上の slice の頂点への射影は厳密な同型。
方針：各次数で空因子との join の単位同型を使い、射影の全単射性を検査する。
規約：標的 X の quasicategory 性を仮定しない。
使われ方：Kerodon 7.1（Tag 02H1） の空図式の極限と終対象の同定。 -/
instance emptySliceProjection_isIso (X : SSet.{u}) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (⊥ : X.Subcomplex).ι) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  rw [isIso_iff_bijective]
  constructor
  · intro a b h
    apply Subtype.ext
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso (Δ[n] : SSet.{u}) X).inv).1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso_inv]
    exact SSet.yonedaEquiv.injective h
  · intro x
    refine ⟨⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso (Δ[n] : SSet.{u}) X).hom ≫ SSet.yonedaEquiv.symm x,
      Subcomplex.isInitialBot.hom_ext _ _⟩, ?_⟩
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] ((⊥ : X.Subcomplex) : SSet.{u}) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso Δ[n] X).hom ≫ SSet.yonedaEquiv.symm x)) = x
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso_inv, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- 概要：空図式の錐の極限性は、その頂点の終対象性と同値。
方針：空図式上の slice の射影の同型を通して終対象性を移す。
規約：IsLimitCone と IsTerminalVertex の既存の定義をそのまま使う。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の空積の公開。 -/
lemma isLimitCone_emptyCone_iff {X : SSet.{u}} (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (emptyCone x) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x := by
  constructor
  · intro h
    have h' := h.map_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (⊥ : X.Subcomplex).ι)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (emptyCone x).vertex at h'
    simpa only [emptyCone_vertex] using h'
  · intro h
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (⊥ : X.Subcomplex).ι)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (emptyCone x).vertex
    simpa only [emptyCone_vertex] using h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
