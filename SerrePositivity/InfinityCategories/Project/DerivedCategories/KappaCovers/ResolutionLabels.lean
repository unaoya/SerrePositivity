module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.SubsetModule
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DependencyPieces
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution

/-!
概要：標準 cell resolution の disk と kernel cell を同じ小宇宙のラベルへ入れる。
方針：全段の添字の直和を shrink し、部分集合の各自由層への逆像を取る。
規約：ラベル選択だけでは微分閉性を主張しない。
使われ方：D-8 d の有限境界 support と依存閉包。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : ModuleCategory R D)

abbrev DGKappaResolutionKernelIndex (n : ℕ) :=
  ModuleKernelCellIndex R D (moduleResolutionStage R D M n).hom

def DGKappaResolutionRawLabel :=
  Sum (ModuleDiskCoverIndex R D M) (Σ n : ℕ, DGKappaResolutionKernelIndex R D M n)

instance : Small.{u} (DGKappaResolutionRawLabel R D M) := by
  unfold DGKappaResolutionRawLabel
  infer_instance

abbrev DGKappaResolutionLabel := Shrink.{u} (DGKappaResolutionRawLabel R D M)

def dgKappaResolutionDiskLabel (i : ModuleDiskCoverIndex R D M) :
    DGKappaResolutionLabel R D M := equivShrink _ (Sum.inl i)

def dgKappaResolutionKernelLabel (n : ℕ) (i : DGKappaResolutionKernelIndex R D M n) :
    DGKappaResolutionLabel R D M := equivShrink _ (Sum.inr ⟨n, i⟩)

lemma dgKappaResolutionDiskLabel_injective :
    Function.Injective (dgKappaResolutionDiskLabel R D M) :=
  (equivShrink _).injective.comp Sum.inl_injective

lemma dgKappaResolutionKernelLabel_injective (n : ℕ) :
    Function.Injective (dgKappaResolutionKernelLabel R D M n) := by
  intro i j h
  have he := Sum.inr_injective ((equivShrink _).injective h)
  exact eq_of_heq (Sigma.mk.inj_iff.mp he).2

def dgKappaResolutionDiskSelection (s : Set (DGKappaResolutionLabel R D M)) :=
  dgKappaResolutionDiskLabel R D M ⁻¹' s

def dgKappaResolutionKernelSelection (s : Set (DGKappaResolutionLabel R D M)) (n : ℕ) :=
  dgKappaResolutionKernelLabel R D M n ⁻¹' s

lemma dgKappaResolutionDiskSelection_small {κ : Cardinal.{u}}
    {s : Set (DGKappaResolutionLabel R D M)} (hs : HasCardinalLT s κ) :
    HasCardinalLT (dgKappaResolutionDiskSelection R D M s) κ :=
  hs.of_injective (fun i => ⟨dgKappaResolutionDiskLabel R D M i.val, i.property⟩)
    (fun _ _ h => Subtype.ext (dgKappaResolutionDiskLabel_injective R D M
      (congrArg Subtype.val h)))

lemma dgKappaResolutionKernelSelection_small {κ : Cardinal.{u}}
    {s : Set (DGKappaResolutionLabel R D M)} (hs : HasCardinalLT s κ) (n : ℕ) :
    HasCardinalLT (dgKappaResolutionKernelSelection R D M s n) κ :=
  hs.of_injective (fun i => ⟨dgKappaResolutionKernelLabel R D M n i.val, i.property⟩)
    (fun _ _ h => Subtype.ext (dgKappaResolutionKernelLabel_injective R D M n
      (congrArg Subtype.val h)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
