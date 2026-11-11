module

public import SerrePositivity.KST.LocalizingInvariants.MappingPathUnitNaturality
public import SerrePositivity.KST.LocalizingInvariants.FiberMappingRelativePath
public import SerrePositivity.KST.Spectra.RawSpectrumMappingLaws
public import SerrePositivity.KST.Spectra.SpectrumMappingComponents

/-!
概要：fibration 置換単位の二つの合成を、元の mapping path 射影に垂直な全 BF 区間で結ぶ。
方針：単射置換の全ての単射への RLP と厳密な mapping path 単位の自然性を適用する。
規約：厳密自然性や π の一致で代用しない。使われ方：指定 cospan prism の二次の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FibrationReplacementComparison

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def unitPath : FiberMapping.RelativePath (fibrationReplacementComparison q)
    (fibrationReplacementUnit p ≫ map p q a b h) (a ≫ fibrationReplacementUnit q) :=
  FiberMapping.relativePath _ _ _
    (fun n ↦ (KanSequence.replacementStage (fibrationPath q) n).projection_rlp)
    (unit_comparison p q a b h)

lemma unitPath_over_projection :
    (SpectrumMappingAcyclic.post X (fibrationReplacementProjection q)).app (Opposite.op ⦋1⦌)
        (unitPath p q a b h).path.edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (vertexOfHom (p ≫ b)) 1 := by
  let c := fibrationReplacementComparison q
  let t := KanSequence.mappingPathTarget (sequenceHom q)
  have hc : RawSpectrumMapping.post X (sequenceHom (fibrationReplacementProjection q)) =
      RawSpectrumMapping.post X c ≫ RawSpectrumMapping.post X t :=
    RawSpectrumMapping.post_comp X c t
  have hs : RawSpectrumMapping.post X (sequenceHom (fibrationReplacementProjection q)) =
      SpectrumMappingAcyclic.post X (fibrationReplacementProjection q) :=
    RawSpectrumMapping.post_spectrum X (fibrationReplacementProjection q)
  have he := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) (unitPath p q a b h).path.edge) hc
  change (RawSpectrumMapping.post X (sequenceHom (fibrationReplacementProjection q))).app _
      (unitPath p q a b h).path.edge =
    (RawSpectrumMapping.post X t).app _
      ((RawSpectrumMapping.post X c).app _ (unitPath p q a b h).path.edge) at he
  have hf : (fibrationReplacementUnit p ≫ map p q a b h) ≫
      fibrationReplacementProjection q = p ≫ b := by
    rw [Category.assoc, map_projection, ← Category.assoc, fibrationReplacement_fac]
  have hv : (RawSpectrumMapping.post X t).app (Opposite.op ⦋0⦌)
        ((RawSpectrumMapping.post X c).app (Opposite.op ⦋0⦌)
          (vertexOfHom (fibrationReplacementUnit p ≫ map p q a b h))) =
      vertexOfHom (p ≫ b) := by
    have hh := congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌)
      (vertexOfHom (fibrationReplacementUnit p ≫ map p q a b h))) hc
    change (RawSpectrumMapping.post X (sequenceHom (fibrationReplacementProjection q))).app _
      (vertexOfHom (fibrationReplacementUnit p ≫ map p q a b h)) = _ at hh
    exact hh.symm.trans ((congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌)
      (vertexOfHom (fibrationReplacementUnit p ≫ map p q a b h))) hs).trans
      ((SpectrumMappingAcyclic.post_vertex _ _).trans (congrArg vertexOfHom hf)))
  have hp := congrArg (fun z ↦ (RawSpectrumMapping.post X t).app (Opposite.op ⦋1⦌) z)
    (unitPath p q a b h).over
  have hk := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map (RawSpectrumMapping.post X t)
    ((RawSpectrumMapping.post X c).app (Opposite.op ⦋0⦌)
      (vertexOfHom (fibrationReplacementUnit p ≫ map p q a b h))) 1
  exact (congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌)
    (unitPath p q a b h).path.edge) hs).symm.trans
      (he.trans (hp.trans (hk.trans (congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z 1) hv))))

end SerrePositivity.KST.LocalizingInvariants.FibrationReplacementComparison
