module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.SkeletonFiltration

/-!
概要：骨格の隣接段へ付け加えるセルの添字と Mathlib の相対セル分解の比較。
方針：低い骨格の包含の相対骨格を通常の骨格と同定し、非退化単体の非所属を使う。
規約：d は付け加えるセルの次元。Mathlib の d 骨格は次元 d 未満。
使われ方：Goerss–Jardine VIII §1。骨格の相対 cofiber を単体ごとの cofiber に分ける準備。

対応節は Kerodon 1.1（Tag 0004）。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
open _root_.SerrePositivity.KST.Spectra.SkeletalCellAttachment

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma lower_eq (K : SSet.{u}) (d : ℕ) :
    skeletonOfMono (K.skeleton d).ι d = K.skeleton d := by
  change Subfunctor.range (K.skeleton d).ι ⊔ K.skeleton d = K.skeleton d
  rw [Subfunctor.range_ι, sup_idem]

lemma upper_eq (K : SSet.{u}) (d : ℕ) :
    skeletonOfMono (K.skeleton d).ι (d + 1) = K.skeleton (d + 1) := by
  change Subfunctor.range (K.skeleton d).ι ⊔ K.skeleton (d + 1) = K.skeleton (d + 1)
  rw [Subfunctor.range_ι, sup_eq_right.mpr (K.skeleton.monotone (Nat.le_succ d))]

/-- 概要：骨格へ次に付け加えるセルの添字はその次元の非退化単体である。
方針：非退化 d 単体が次元 d 未満の骨格に属さないことから相対セル条件を得る。
規約：退化単体はセルの添字に含めない。
使われ方：Goerss–Jardine VIII §1。fiber の積の添字の具体化。 -/
def cellEquiv (K : SSet.{u}) (d : ℕ) :
    relativeCellComplexOfMono.Cell (K.skeleton d).ι d ≃ K.nonDegenerate d where
  toFun c := ⟨c.simplex, c.nonDegenerate⟩
  invFun x := {
    simplex := x.1
    nonDegenerate := x.2
    notMem := by
      rintro ⟨y, hy⟩
      have hm : x.1 ∈ (K.skeleton d).obj _ := by
        rw [← hy]
        exact y.property
      exact Nat.lt_irrefl d ((K.mem_skeleton_obj_iff_of_nonDegenerate x d).mp hm) }
  left_inv c := by cases c; rfl
  right_inv x := rfl

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
