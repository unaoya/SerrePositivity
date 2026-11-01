module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FiniteQuiver

/-!
# 元の有限頂点の包含の厳密な恒等・合成則

概要：元の包含の自由関手と全体への射影が厳密に整合する。
方針：所属証明の一意性と元の自由関手の恒等・合成則を使う。
規約：元の生成辺と射列の写像を変更しない。
使われ方：有限部分集合で添字付けた hammock 図式。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FiniteQuiver
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] {S R U : Finset Q}

lemma subsetPrefunctor_refl (S : Finset Q) : letI := quiver S
    subsetPrefunctor (Finset.Subset.refl S) = 𝟭q (Vertex S) := rfl

lemma subsetPrefunctor_comp (h : S ⊆ R) (k : R ⊆ U) :
    letI := quiver S
    letI := quiver R
    letI := quiver U
    subsetPrefunctor h ⋙q subsetPrefunctor k = subsetPrefunctor (h.trans k) := rfl

lemma subsetPrefunctor_inclusion (h : S ⊆ R) :
    letI := quiver S
    letI := quiver R
    subsetPrefunctor h ⋙q inclusion R = inclusion S := rfl

lemma subsetFunctor_refl (S : Finset Q) : letI := quiver S
    subsetFunctor (Finset.Subset.refl S) = 𝟭 (Paths (Vertex S)) := by
  let := quiver S
  exact Cat.freeMap_id (Vertex S)

lemma subsetFunctor_comp (h : S ⊆ R) (k : R ⊆ U) :
    letI := quiver S
    letI := quiver R
    letI := quiver U
    subsetFunctor (h.trans k) = subsetFunctor h ⋙ subsetFunctor k := by
  let := quiver S
  let := quiver R
  let := quiver U
  exact Cat.freeMap_comp (subsetPrefunctor h) (subsetPrefunctor k)

lemma subsetFunctor_pathInclusion (h : S ⊆ R) :
    letI := quiver S
    letI := quiver R
    subsetFunctor h ⋙ pathInclusion R = pathInclusion S := by
  let := quiver S
  let := quiver R
  exact (Cat.freeMap_comp (subsetPrefunctor h) (inclusion R)).symm

end SerrePositivity.EInfinity.Hammock.FiniteQuiver
