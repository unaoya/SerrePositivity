module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionBoundaryExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CellularNaturalComparison
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

/-!
概要：一般の解像の単射保存と、全単体集合上での射影の同値性。
方針：単射を境界の包含によるセル分解で表し、解像の余極限保存を使って単射性を移す。
規約：同値性は任意の quasicategory への前合成による条件。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、補助解像の一般の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits HomotopicalAlgebra SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単射を解像で写す基本セルの貼り付けは、全体も単射へ写る。
方針：セルの余積を解像で写し、単射な余積の pushout の単射性を使う。
規約：貼り付けるセルの添字型の大きさは単体の宇宙 u。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、セル分解の各段の単射性。 -/
lemma coherentResolution_map_mono_of_attachCells {α : Type v} {A B : α → SSet.{u}}
    (g : (i : α) → A i ⟶ B i) {X Y : SSet.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} g f) (hg : ∀ i, Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (g i))) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map f) := by
  let τ : Discrete.functor (fun i : c.ι ↦ A (c.π i)) ⟶
      Discrete.functor (fun i : c.ι ↦ B (c.π i)) :=
    Discrete.natTrans (fun i ↦ g (c.π i.as))
  have hm : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map c.m) := by
    change (MorphismProperty.monomorphisms SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map c.m)
    refine MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := MorphismProperty.monomorphisms SSet.{u})
      _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.mapCocone c.cofan₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.mapCocone c.cofan₂)
      (isColimitOfPreserves _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution c.isColimit₁)
      (isColimitOfPreserves _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution c.isColimit₂)
      (CategoryTheory.Functor.whiskerRight τ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution)
      (fun i ↦ hg (c.π i.as)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map c.m) ?_
    intro i
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (c.cofan₁.inj i.as) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map c.m =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (g (c.π i.as)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (c.cofan₂.inj i.as)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, c.hm]
  haveI := hm
  exact Adhesive.mono_of_isPushout_of_mono_left (c.isPushout.map _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution).flip

/-- 概要：一般の解像は任意の単射を単射へ写す。
方針：単射を境界の包含のセル分解で表し、解像後の可算の単射の合成にする。
規約：標準単体の境界の計算から全ての単射へ拡張する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、一般の射影のセルによる比較の入力。 -/
lemma coherentResolution_map_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map f) := by
  let c := SSet.relativeCellComplexOfMono f
  haveI : PreservesWellOrderContinuousOfShape ℕ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.{u} :=
    { preservesColimitsOfShape := fun _ _ ↦ inferInstance }
  let t : (MorphismProperty.monomorphisms SSet.{u}).TransfiniteCompositionOfShape ℕ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map f) :=
    { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.map _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution
      map_mem j hj := coherentResolution_map_mono_of_attachCells _ (c.attachCells j hj)
        (fun _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution_map_boundary_ι_mono j) }
  haveI : SuccOrder (ULift.{u} ℕ) := SuccOrder.ofOrderIso (ULift.orderIso.{u}).symm
  let t' := t.ofOrderIso (ULift.orderIso.{u} : ULift.{u} ℕ ≃o ℕ)
  exact (MorphismProperty.monomorphisms SSet.{u}).transfiniteCompositionsOfShape_le
    (ULift.{u} ℕ) _ t'.mem

/-- 概要：解像の関手は単射保存の標準インスタンスを持つ。
方針：任意の単射の像について証明した単射性を登録する。
規約：以後は関手の map_mono で利用できる。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、自然な比較のセルによる拡張。 -/
instance coherentResolution_preservesMonomorphisms :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.{u}.PreservesMonomorphisms where
  preserves f _ := coherentResolution_map_mono f

/-- 概要：始対象上で一般の解像の射影は前合成による同値。
方針：左随伴が始対象を保存するため、射影は二つの始対象間の同型。
規約：通常の単体集合の圏の始対象。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、自然な比較のセル帰納法の基底。 -/
lemma coherentResolutionProjectionAll_initial_isPrecompositionEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.{u}.app (⊥_ SSet.{u})) := by
  let h := initialIsInitial (C := SSet.{u})
  let hF := h.isInitialObj _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution
  let e := hF.uniqueUpToIso h
  have he : e.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app (⊥_ SSet.{u}) := hF.hom_ext _ _
  rw [← he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e

/-- 概要：任意の単体集合上で一般の解像の射影は前合成による同値。
方針：単射と余極限の保存、始対象と標準単体での比較を使ってセル帰納法を適用する。
規約：始域の解像自体の quasicategory 性は仮定しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、coherent Hom の比較の一般の補助解像。 -/
lemma coherentResolutionProjectionAll_isPrecompositionEquivalence (X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_natComponent_of_stdSimplex _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll
    coherentResolutionProjectionAll_initial_isPrecompositionEquivalence
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_std_isPrecompositionEquivalence X

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.2.2.7"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_isPrecompositionEquivalence
attribute [cite HTT "2.2.2.8"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_isPrecompositionEquivalence
