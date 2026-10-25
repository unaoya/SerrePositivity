module
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.ResolutionSupport

/-!
概要：各 kernel cell の境界の有限 support をセル依存関係として固定する。
方針：disk には追加依存先を置かず、kernel cell には前段の境界 support を置く。
規約：作用係数の濃度は数えず、実セルのラベルだけを数える。
使われ方：D-8 d の κ-small な依存閉部分集合の添字。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : ModuleCategory R D)

def dgKappaResolutionDependencies (a : DGKappaResolutionLabel R D M) :
    Set (DGKappaResolutionLabel R D M) :=
  match (equivShrink (DGKappaResolutionRawLabel R D M)).symm a with
  | Sum.inl _ => ∅
  | Sum.inr ⟨n, j⟩ =>
    ↑(dgKappaResolutionElementSupport R D M n j.1 (j.2.1 + 1) j.2.2.val.val)

lemma dgKappaResolutionDependencies_finite (a : DGKappaResolutionLabel R D M) :
    (dgKappaResolutionDependencies R D M a).Finite := by
  unfold dgKappaResolutionDependencies
  split
  · exact Set.finite_empty
  · exact Finset.finite_toSet _

lemma dgKappaResolutionDependencies_small {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
    (a : DGKappaResolutionLabel R D M) :
    HasCardinalLT (dgKappaResolutionDependencies R D M a) κ := by
  letI := (dgKappaResolutionDependencies_finite R D M a).fintype
  exact hasCardinalLT_of_finite _ _ hκ.le

abbrev DGKappaResolutionPieces (κ : Cardinal.{u}) [Fact κ.IsRegular] :=
  DGKappaDependencyPieces (dgKappaResolutionDependencies R D M) (κ := κ)

lemma dgKappaResolutionKernel_supported
    (s : Set (DGKappaResolutionLabel R D M))
    (hs : ∀ a ∈ s, dgKappaResolutionDependencies R D M a ⊆ s)
    (n : ℕ) (j : dgKappaResolutionKernelSelection R D M s n) :
    DGKappaResolutionElementSupported R D M s n j.val.1 (j.val.2.1 + 1)
      j.val.2.2.val.val := by
  apply dgKappaResolutionElementSupport_spec R D M
  have h := hs (dgKappaResolutionKernelLabel R D M n j.val) j.property
  simpa only [dgKappaResolutionDependencies, dgKappaResolutionKernelLabel,
    Equiv.symm_apply_apply] using h

lemma dgKappaResolutionPieces_isCardinalFiltered (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    IsCardinalFiltered (DGKappaResolutionPieces R D M κ) κ :=
  dgKappaDependencyPieces_isCardinalFiltered _

lemma dgKappaResolutionPieces_cover {κ : Cardinal.{u}} [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ) (a : DGKappaResolutionLabel R D M) :
    ∃ s : DGKappaResolutionPieces R D M κ, a ∈ s.val :=
  dgKappaDependencyPieces_cover _ hκ (dgKappaResolutionDependencies_small R D M hκ) a

end SerrePositivity.InfinityCategories
