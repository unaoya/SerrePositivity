module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.SkeletonFiltration

/-!
概要：単射は骨格を反映し、骨格への制限も単射となる。
方針：単射による非退化性の保存で骨格の次元条件を反映し、包含との可換式で単射性を移す。
規約：骨格は部分複体として定義した既存の SkeletonFiltration を使う。
使われ方：Goerss–Jardine VIII §1。有限骨格の相対 latching の共通部分の計算。

対応節は Kerodon 1.1（Tag 0004）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.SkeletonFiltration
end SerrePositivity.KST.Spectra.SkeletonFiltration
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
open _root_.SerrePositivity.KST.Spectra.SkeletonFiltration
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 単射による骨格の逆像は元の骨格そのもの。 -/
lemma preimage_skeleton {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (n : ℕ) :
    (Y.skeleton n).preimage f = X.skeleton n := by
  apply le_antisymm
  · rw [Subcomplex.le_iff_contains_nonDegenerate]
    intro d x hx
    have hfx : f.app _ x.val ∈ Y.nonDegenerate d :=
      (SSet.nonDegenerate_iff_of_mono f x.val).2 x.property
    have hd : d < n := (Y.mem_skeleton_obj_iff_of_nonDegenerate ⟨_, hfx⟩ n).1 hx
    exact X.mem_skeleton x.val hd
  · exact (Subcomplex.image_le_iff _ f _).1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.image_le f n)

/-- 単射の骨格の像は、全体の像と標的の骨格の共通部分。 -/
lemma image_skeleton {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (n : ℕ) :
    (X.skeleton n).image f = Subcomplex.range f ⊓ Y.skeleton n := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.preimage_skeleton f n]
  ext j y
  change (∃ x, f.app j x ∈ (Y.skeleton n).obj j ∧ f.app j x = y) ↔
    (∃ x, f.app j x = y) ∧ y ∈ (Y.skeleton n).obj j
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, hx⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩

/-- 骨格関手は実際の単射を単射へ送る。 -/
lemma map_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (n : ℕ) : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.map f n) := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.map f n ≫ (Y.skeleton n).ι) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.map_ι]
    infer_instance
  exact mono_of_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.map f n) (Y.skeleton n).ι

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletonFiltration.image_skeleton := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.image_skeleton

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletonFiltration.map_mono := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.map_mono

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletonFiltration.preimage_skeleton := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.preimage_skeleton
