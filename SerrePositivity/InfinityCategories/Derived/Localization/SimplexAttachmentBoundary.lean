module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.F1B.Quasicategory.SimplexTerminalCoconeExtension
public import SerrePositivity.InfinityCategories.Core.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Core.InnerAnodyneEquivalence
public import SerrePositivity.InfinityCategories.Core.PrecompositionLifting

/-!
概要：有限単体とその終端からの次辺を、共有点を保持する実部分図式として貼る。
方針：終点包含の像と空部分複体の pushout-join を用い、inner anodyne 性を証明する。
規約：零次を含む全次数、二つの元の包含、共有点の厳密等号を保持する。
使われ方：c5 の有限線型図式とその全比較を一段延長する工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet MorphismProperty
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Localization
open SerrePositivity.KST.LocalizingInvariants

/-- 元の最後の点包含の像。 -/
def simplexLastVertex (n : ℕ) : (Δ[n] : SSet.{u}).Subcomplex :=
  Subfunctor.range (simplexLastPoint n)

/-- 最後の点はその像と同型。 -/
def simplexLastPointRangeIso (n : ℕ) :
    (Δ[0] : SSet.{u}) ≅ (simplexLastVertex n : SSet.{u}) := by
  have := Subfunctor.instIsIsoFunctorTypeToRangeOfMono (simplexLastPoint.{u} n)
  exact asIso (Subfunctor.toRange (simplexLastPoint n))

@[reassoc]
lemma simplexLastPointRangeIso_hom_ι (n : ℕ) :
    (simplexLastPointRangeIso n).hom ≫ (simplexLastVertex n).ι =
      simplexLastPoint.{u} n := rfl

/-- 元の終点の像の包含も right anodyne。 -/
lemma simplexLastVertex_rightAnodyne (n : ℕ) :
    rightAnodyneExtensions (simplexLastVertex.{u} n).ι := by
  have ht := F1B.terminalPoint_rightAnodyne (stdSimplex_last_isTerminalVertex.{u} n)
  exact (rightAnodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (simplexLastPointRangeIso n) (Iso.refl _) (by rfl))).mp ht

/-- 前段の全単体と、その終点から新頂点への元の次辺の和。 -/
def simplexAttachmentBoundary (n : ℕ) : (join (Δ[n] : SSet.{u}) Δ[0]).Subcomplex :=
  joinUnion (simplexLastVertex n) (⊥ : (Δ[0] : SSet.{u}).Subcomplex)

/-- 前段の全単体の元の包含。 -/
def simplexAttachmentPrefix (n : ℕ) :
    (Δ[n] : SSet.{u}) ⟶ (simplexAttachmentBoundary n : SSet.{u}) :=
  (joinEmptyIso Δ[n] Δ[0]).inv ≫
    joinUnionRight (simplexLastVertex n) (⊥ : (Δ[0] : SSet.{u}).Subcomplex)

/-- 元の次辺の包含。始域は二点の join として固定する。 -/
def simplexAttachmentLastEdge (n : ℕ) :
    join (Δ[0] : SSet.{u}) Δ[0] ⟶ (simplexAttachmentBoundary n : SSet.{u}) :=
  joinMap (simplexLastPointRangeIso n).hom (𝟙 Δ[0]) ≫
    joinUnionLeft (simplexLastVertex n) (⊥ : (Δ[0] : SSet.{u}).Subcomplex)

@[reassoc]
lemma simplexAttachmentPrefix_ι (n : ℕ) :
    simplexAttachmentPrefix n ≫ (simplexAttachmentBoundary n).ι =
      joinInl (Δ[n] : SSet.{u}) Δ[0] := by
  unfold simplexAttachmentPrefix simplexAttachmentBoundary
  rw [Category.assoc, joinUnionRight_ι, joinEmptyIso_inv,
    joinInl_joinMap, Category.id_comp]

@[reassoc]
lemma simplexAttachmentLastEdge_ι (n : ℕ) :
    simplexAttachmentLastEdge n ≫ (simplexAttachmentBoundary n).ι =
      joinMap (simplexLastPoint.{u} n) (𝟙 Δ[0]) := by
  unfold simplexAttachmentLastEdge simplexAttachmentBoundary
  rw [Category.assoc, joinUnionLeft_ι, ← joinMap_comp,
    simplexLastPointRangeIso_hom_ι, Category.id_comp]

/-- 二つの元の包含は、指定された同じ終点を厳密に共有する。 -/
lemma simplexAttachmentBoundary_comm (n : ℕ) :
    joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ simplexAttachmentLastEdge n =
      simplexLastPoint n ≫ simplexAttachmentPrefix n := by
  apply (cancel_mono (simplexAttachmentBoundary n).ι).mp
  rw [Category.assoc, simplexAttachmentLastEdge_ι, Category.assoc,
    simplexAttachmentPrefix_ι, joinInl_joinMap]

/-- 前段と次辺の和は、元の共有点に沿う実 pushout。 -/
lemma simplexAttachmentBoundary_isPushout (n : ℕ) :
    IsPushout (joinInl (Δ[0] : SSet.{u}) Δ[0]) (simplexLastPoint n)
      (simplexAttachmentLastEdge n) (simplexAttachmentPrefix n) := by
  let R := simplexLastVertex.{u} n
  let e := simplexLastPointRangeIso.{u} n
  apply (joinUnion_isPushout R (⊥ : (Δ[0] : SSet.{u}).Subcomplex)).of_iso'
    (e ≪≫ (joinEmptyIso R Δ[0]).symm) (joinIso e (Iso.refl Δ[0]))
    (joinEmptyIso Δ[n] Δ[0]).symm (Iso.refl _)
  · simp only [Iso.trans_hom, Iso.symm_hom, joinEmptyIso_inv, joinIso,
      Iso.refl_hom]
    rw [Category.assoc, joinInl_joinMap, joinInl_joinMap, Category.id_comp]
  · simp only [Iso.trans_hom, Iso.symm_hom, joinEmptyIso_inv]
    rw [Category.assoc, joinInl_joinMap,
      ← Category.assoc, simplexLastPointRangeIso_hom_ι]
  · rfl
  · rfl

/-- この実部分図式から一段長い全単体への包含は inner anodyne。 -/
lemma simplexAttachmentBoundary_innerAnodyne (n : ℕ) :
    innerAnodyneExtensions (simplexAttachmentBoundary.{u} n).ι :=
  joinUnion_innerAnodyne_of_rightAnodyne _ _ (simplexLastVertex_rightAnodyne n)

/-- 全比較の制限は、両端と任意の指定部分族を保持する自明 Kan ファイブレーション。 -/
instance simplexAttachmentRestriction_trivialKanFibration (n : ℕ)
    (X : SSet.{u}) [Quasicategory X] :
    TrivialKanFibration ((pre (simplexAttachmentBoundary n).ι).app X) :=
  trivialKanFibration_pre_of_innerAnodyne _ (simplexAttachmentBoundary_innerAnodyne n) X

end SerrePositivity.InfinityCategories.Derived.Localization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentBoundary (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentBoundary := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentBoundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentBoundary_comm := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentBoundary_comm

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentBoundary_innerAnodyne := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentBoundary_innerAnodyne

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentBoundary_isPushout := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentBoundary_isPushout

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentLastEdge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentLastEdge := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentLastEdge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentLastEdge_ι := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentLastEdge_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentLastEdge_ι_assoc := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentLastEdge_ι_assoc

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentPrefix (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentPrefix := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentPrefix

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentPrefix_ι := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentPrefix_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentPrefix_ι_assoc := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentPrefix_ι_assoc

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentRestriction_trivialKanFibration (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentRestriction_trivialKanFibration := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentRestriction_trivialKanFibration

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexLastPointRangeIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexLastPointRangeIso := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexLastPointRangeIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexLastPointRangeIso_hom_ι := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexLastPointRangeIso_hom_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexLastPointRangeIso_hom_ι_assoc := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexLastPointRangeIso_hom_ι_assoc

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexLastVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexLastVertex := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexLastVertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexLastVertex_rightAnodyne := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexLastVertex_rightAnodyne

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexLastPointRangeIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexLastPointRangeIso._proof_1
