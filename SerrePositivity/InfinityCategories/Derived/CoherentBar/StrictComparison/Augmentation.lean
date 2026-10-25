module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationTheta
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedHomDegrees

/-!
概要：実正規化 coherent bar から strict 余錐の頂点への標準 dg 加群射を構成する。
方針：graded augmentation の閉零要素を同じ MC 変更へ移し、theta 消滅で閉性を示す。
規約：元の正規化 bar 加群と全 dg 加群 Hom を保持する。
使われ方：filtered strict 余極限比較 C1 の標準射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [Category J] (F : J ⥤ ModuleCategory R D) (c : Cocone F)

def dgCoherentBarStrictAugmentationElement :
    (moduleHom R D (dgCoherentBarStrictNormalizedModule R D F)
      (ForgetEnrichment.to (Complex R) c.pt)).X 0 :=
  (dgCoherentBarNormalizedHomDegreeEquiv R D (dgCoherentBarStrictDiagram R D F)
    (dgCoherentBarMaurerCartan_unconditional R D (dgCoherentBarStrictDiagram R D F))
    (ForgetEnrichment.to (Complex R) c.pt) 0).symm
      (closedHomEquiv R (RightModule R D)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)) c.pt
        (dgCoherentBarStrictAugmentationGraded R D F c)).val

lemma dgCoherentBarStrictAugmentationElement_closed :
    (moduleHom R D (dgCoherentBarStrictNormalizedModule R D F)
      (ForgetEnrichment.to (Complex R) c.pt)).d 0 1
      (dgCoherentBarStrictAugmentationElement R D F c) = 0 := by
  let G := dgCoherentBarStrictDiagram R D F
  let hMC := dgCoherentBarMaurerCartan_unconditional R D G
  let N := ForgetEnrichment.to (Complex R) c.pt
  let z := (closedHomEquiv R (RightModule R D)
    (dgCoherentBarNormalizedGraded R D G) c.pt
      (dgCoherentBarStrictAugmentationGraded R D F c)).val
  apply (dgCoherentBarNormalizedHomDegreeEquiv R D G hMC N 1).injective
  rw [map_zero]
  have hd := dgCoherentBarNormalizedHomDegreeEquiv_d R D G hMC N 0
    (dgCoherentBarStrictAugmentationElement R D F c)
  change dgCoherentBarNormalizedHomDegreeEquiv R D G hMC N 1
    ((moduleHom R D (dgCoherentBarStrictNormalizedModule R D F) N).d 0 1
      (dgCoherentBarStrictAugmentationElement R D F c)) = _ at hd
  rw [hd]
  have he : dgCoherentBarNormalizedHomDegreeEquiv R D G hMC N 0
      (dgCoherentBarStrictAugmentationElement R D F c) = z :=
    (dgCoherentBarNormalizedHomDegreeEquiv R D G hMC N 0).apply_symm_apply z
  rw [he]
  have hz : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G)) N).d 0 1 z = 0 :=
    (closedHomEquiv R (RightModule R D)
      (dgCoherentBarNormalizedGraded R D G) c.pt
        (dgCoherentBarStrictAugmentationGraded R D F c)).property
  erw [hz, zero_add]
  have ht := dgCoherentBarStrictAugmentation_postNormalizedTheta R D F c
  erw [dgStrictPostcompose_eq_compose R D] at ht
  erw [ht, smul_zero]

def dgCoherentBarStrictAugmentation :
    ForgetEnrichment.of (Complex R) (dgCoherentBarStrictNormalizedModule R D F) ⟶ c.pt :=
  moduleMorphismOfCycle R D (dgCoherentBarStrictAugmentationElement R D F c)
    (dgCoherentBarStrictAugmentationElement_closed R D F c)

def dgCoherentBarStrictColimitAugmentation [HasColimit F] :
    ForgetEnrichment.of (Complex R) (dgCoherentBarStrictNormalizedModule R D F) ⟶ colimit F :=
  dgCoherentBarStrictAugmentation R D F (colimit.cocone F)

end SerrePositivity.InfinityCategories
