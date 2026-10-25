module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceTerminalCoslice
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceProjection
public import SerrePositivity.InfinityCategories.F2.Compact.FullCoslicePullback
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulBaseChange
public import SerrePositivity.InfinityCategories.F2.Presentable.CoslicePostcompIdentity

/-!
概要：固定始域圏の反復 coslice から、元の終域の coslice への比較を構成する。
方針：全部分包含の引き戻しと全 coslice の left fibration による比較を合成する。
規約：終域射影自体を left fibration とはしない。
使われ方：HTT 5.5.5.12–14 の retraction の全写像空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 固定始域圏の点の下の coslice から、元の終域の下の coslice への実際の比較。 -/
def generatedSourceUnderTarget (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) :
    sliceUnder (SSet.yonedaEquiv.symm s) ⟶
      sliceUnder (SSet.yonedaEquiv.symm ((generatedSourceTarget edges x).app _ s)) :=
  stableCoslicePostcomp (SSet.yonedaEquiv.symm s) (generatedSourceTarget edges x)
    _ (SSet.yonedaEquiv_symm_comp s (generatedSourceTarget edges x))

/-- 比較は同じ恒等余錐を厳密に保持する。 -/
lemma generatedSourceUnderTarget_identity (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) :
    (generatedSourceUnderTarget edges x s).app _ (cosliceIdentityCone s) =
      cosliceIdentityCone ((generatedSourceTarget edges x).app _ s) :=
  coslicePostcomp_identity (generatedSourceTarget edges x) s

/-- 比較は元の全写像空間を保持する。 -/
lemma generatedSourceUnderTarget_isFullyFaithful (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) :
    IsFullyFaithful (generatedSourceUnderTarget edges x s) := by
  let a := SSet.yonedaEquiv.symm s
  let j := generatedSourceInclusion edges x
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  have hj : InnerFibration j :=
    F1B.EquivalenceLifting.innerFibration (generatedSourceInclusion_equivalenceLifting edges x)
  have hpull := Compact.fullSliceUnder_isPullback
    (X := sliceUnder (SSet.yonedaEquiv.symm x))
    (fun c : JoinCocone (SSet.yonedaEquiv.symm x) ↦
      (JoinCocone.leg c (𝟙 Δ[0])).edge ∈ generatedEdges edges) a
  have hpb : IsFullyFaithful (pullback.snd j (sliceUnderProjection (a ≫ j))) :=
    (generatedSourceInclusion_isFullyFaithful edges x).pullback_snd _
  have : InnerFibration (pullback.snd j (sliceUnderProjection (a ≫ j))) :=
    ⟨innerFibrations.pullback_snd j _ (InnerFibration.mem (q := j))⟩
  have : Quasicategory (pullback j (sliceUnderProjection (a ≫ j))) :=
    quasicategory_of_innerFibration (pullback.snd j (sliceUnderProjection (a ≫ j)))
  have hfirst : IsFullyFaithful (sliceUnderPostcomp a j) := by
    have h := (qCatEquivalenceOfIso hpull.isoPullback).isFullyFaithful.comp hpb
    change IsFullyFaithful (hpull.isoPullback.hom ≫
      pullback.snd j (sliceUnderProjection (a ≫ j))) at h
    have heq : hpull.isoPullback.hom ≫
        pullback.snd j (sliceUnderProjection (a ≫ j)) = sliceUnderPostcomp a j :=
      hpull.isoPullback_hom_snd
    exact heq ▸ h
  have : TrivialKanFibration (sliceUnderPostcomp (a ≫ j) p) :=
    sliceUnderPostcomp_trivialKanFibration (a ≫ j) p
  have hsecond : IsFullyFaithful (sliceUnderPostcomp (a ≫ j) p) :=
    (isQCatEquivalence_of_trivialKanFibration _).isFullyFaithful
  have hraw : IsFullyFaithful (sliceUnderPostcomp a (j ≫ p)) := by
    exact hfirst.comp hsecond
  exact hraw.comp (qCatEquivalenceOfIso (eqToIso (congrArg sliceUnder
    (SSet.yonedaEquiv_symm_comp s (generatedSourceTarget edges x))))).isFullyFaithful

/-- 終対象の恒等余錐への写像空間の可縮性を、元の終域の coslice に移す。 -/
lemma generatedSourceUnderTarget_terminal_mapping_contractible
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s)
    (c : (sliceUnder (SSet.yonedaEquiv.symm s)) _⦋0⦌) :
    IsContractibleKan (pinchedHom
      ((generatedSourceUnderTarget edges x s).app _ c)
      (cosliceIdentityCone ((generatedSourceTarget edges x).app _ s))) := by
  have h := ((generatedSourceUnderTarget_isFullyFaithful edges x s) c
    (cosliceIdentityCone s)).isContractibleKan_iff.mp
      (generatedSource_terminal_identity_mapping_contractible edges x s hs c)
  rwa [generatedSourceUnderTarget_identity] at h

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
