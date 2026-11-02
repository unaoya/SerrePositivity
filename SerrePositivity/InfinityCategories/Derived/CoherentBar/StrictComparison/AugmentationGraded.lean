module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Diagram
public import SerrePositivity.DifferentialGraded.Module.Graded

/-!
概要：strict 図式の余錐から、正規化 graded bar の標準 augmentation を作る。
方針：零次元因子では余錐の脚を使い、正次元因子では零にする。
規約：この葉の射は内部微分についての射。bar 微分についての閉性は別に証明する。
使われ方：正規化 bar から strict 余極限への標準射の係数。
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

def dgCoherentBarStrictAugmentationRawColumn : (s : dgCoherentBarIndex (nerve J)) →
    dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) s ⟶ c.pt
  | ⟨0, s⟩ => (moduleShiftZeroIsoObj R D
      (ForgetEnrichment.to (Complex R) (F.obj (s.obj 0)))).hom ≫ c.ι.app (s.obj 0)
  | ⟨n + 1, _⟩ => 0

def dgCoherentBarStrictAugmentationGraded :
    dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F) ⟶ c.pt :=
  Sigma.desc (fun s => dgCoherentBarStrictAugmentationRawColumn R D F c s.val)

def dgCoherentBarStrictAugmentationRawGraded :
    dgCoherentBarGraded R D (dgCoherentBarStrictDiagram R D F) ⟶ c.pt :=
  Sigma.desc (dgCoherentBarStrictAugmentationRawColumn R D F c)

@[reassoc] lemma dgCoherentBarStrictAugmentationGraded_ι
    (s : dgCoherentBarNormalizedIndex (nerve J)) :
    Sigma.ι (dgCoherentBarNormalizedFamily R D (dgCoherentBarStrictDiagram R D F)) s ≫
      dgCoherentBarStrictAugmentationGraded R D F c =
        dgCoherentBarStrictAugmentationRawColumn R D F c s.val :=
  Sigma.ι_comp_desc _ _

@[reassoc] lemma dgCoherentBarStrictAugmentationRawGraded_ι
    (s : dgCoherentBarIndex (nerve J)) :
    Sigma.ι (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F)) s ≫
      dgCoherentBarStrictAugmentationRawGraded R D F c =
        dgCoherentBarStrictAugmentationRawColumn R D F c s :=
  Sigma.ι_comp_desc _ _

lemma dgCoherentBarStrictAugmentation_projection :
    dgCoherentBarNormalizedProjection R D (dgCoherentBarStrictDiagram R D F) ≫
        dgCoherentBarStrictAugmentationGraded R D F c =
      dgCoherentBarStrictAugmentationRawGraded R D F c := by
  classical
  apply Sigma.hom_ext
  intro s
  by_cases h : s.2 ∈ (nerve J).nonDegenerate s.1
  · rw [dgCoherentBarNormalizedProjection_ι_assoc R D _ ⟨s, h⟩,
      dgCoherentBarStrictAugmentationGraded_ι, dgCoherentBarStrictAugmentationRawGraded_ι]
  · have hd : s.2 ∈ (nerve J).degenerate s.1 := by
      simpa only [SSet.nonDegenerate, Set.mem_compl_iff, not_not] using h
    rw [dgCoherentBarNormalizedProjection_ι_degenerate_assoc R D _ ⟨s, hd⟩,
      zero_comp, dgCoherentBarStrictAugmentationRawGraded_ι]
    rcases s with ⟨n, s⟩
    cases n with
    | zero => simpa only [SSet.degenerate_zero, Set.mem_empty_iff_false] using hd
    | succ n => rfl

end SerrePositivity.InfinityCategories
