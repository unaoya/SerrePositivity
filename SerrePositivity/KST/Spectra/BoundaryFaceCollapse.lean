module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.HornBoundaryDecomposition
public import SerrePositivity.KST.Spectra.SphereSimplex

/-!
概要：標準単体の境界のホーンを潰し、残る面を球面へ送る射。
方針：ホーンと欠けた面の pushout で、ホーンを基点へ、面を境界の商へ送る。
規約：残る面の境界は共通部分から厳密に因子分解する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。相対三角形を二次元 cell として表示する付着写像。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：ホーンの定数射と欠けた面の球面への商写像は共通部分で一致する。
方針：共通部分を面の境界へ戻して cofiber の基点条件を使う。
規約：球面の次数は n。
使われ方：Goerss–Jardine I §7。境界上の付着写像の貼り合わせ条件。 -/
theorem boundaryFaceCollapse_compatibility (n : ℕ) (i : Fin (n + 2)) :
    Subcomplex.homOfLE (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlap.{u} n i ≤ horn (n + 1) i from inf_le_left) ≫
      (toUnit (horn.{u} (n + 1) i : SSet.{u}) ≫ (PointedSimplicialSet.sphere.{u} n).hom) =
    Subcomplex.homOfLE (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlap.{u} n i ≤ stdSimplex.face {i}ᶜ from inf_le_right) ≫
      ((stdSimplex.faceSingletonComplIso i).inv ≫
        PointedObject.cofiberQuotient (boundary.{u} n).ι) := by
  rw [comp_toUnit_assoc, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlapToBoundary_ι,
    Category.assoc, PointedObject.cofiberQuotient_condition, comp_toUnit_assoc]
  rfl

/-- 概要：境界のホーンを潰して残る面を球面へ送る実際の射。
方針：ホーンと欠けた面の pushout の普遍性で貼り合わせる。
規約：普通の単体集合の射であり Kan 性は要求しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。相対 cell の付着写像。 -/
def boundaryFaceCollapse (n : ℕ) (i : Fin (n + 2)) :
    (boundary.{u} (n + 1) : SSet.{u}) ⟶ (PointedSimplicialSet.sphere.{u} n).right :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornBoundaryPushout n i).desc
    (toUnit (horn.{u} (n + 1) i : SSet.{u}) ≫ (PointedSimplicialSet.sphere.{u} n).hom)
    ((stdSimplex.faceSingletonComplIso i).inv ≫ PointedObject.cofiberQuotient (boundary.{u} n).ι)
    (boundaryFaceCollapse_compatibility n i)

/-- 概要：付着写像はホーン全体を基点へ送る。
方針：pushout のホーン側の標準射での計算を使う。
規約：厳密な単体集合の射の等式。
使われ方：Goerss–Jardine I §7。ホーンの cofiber への降下の条件。 -/
@[reassoc (attr := simp)]
theorem boundaryFaceCollapse_horn (n : ℕ) (i : Fin (n + 2)) :
    Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.horn_le_simplexBoundary n i) ≫ boundaryFaceCollapse.{u} n i =
      toUnit (horn.{u} (n + 1) i : SSet.{u}) ≫ (PointedSimplicialSet.sphere.{u} n).hom :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornBoundaryPushout n i).inl_desc _ _ _

/-- 概要：付着写像は残る面で標準の球面への商写像に一致する。
方針：面の標準単体との同型を通して pushout の面側の式を使う。
規約：面の添字は i。
使われ方：Goerss–Jardine I §7、BF 1978 §2。相対三角形の対角辺の同定。 -/
@[reassoc (attr := simp)]
theorem boundaryFaceCollapse_face (n : ℕ) (i : Fin (n + 2)) :
    boundary.ι i ≫ boundaryFaceCollapse.{u} n i =
      PointedObject.cofiberQuotient (boundary.{u} n).ι := by
  have hi : boundary.ι i = (stdSimplex.faceSingletonComplIso.{u} i).hom ≫
      Subcomplex.homOfLE (face_singleton_compl_le_boundary i) := by
    change boundary.ι i = (stdSimplex.faceSingletonComplIso.{u} i).hom ≫ boundary.faceι i
    rw [← boundary.faceSingletonComplIso_inv_ι, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  rw [hi, Category.assoc, boundaryFaceCollapse]
  rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornBoundaryPushout n i).inr_desc]
  exact Iso.hom_inv_id_assoc _ _

/-- 概要：付着写像は残る面以外の各面を基点へ送る。
方針：各面をホーン経由で因子分解してホーン上の式を使う。
規約：j≠i。
使われ方：Goerss–Jardine I §7。相対三角形の二つの外辺の基点条件。 -/
@[reassoc (attr := simp)]
theorem boundaryFaceCollapse_other_face (n : ℕ) (i j : Fin (n + 2)) (hji : j ≠ i) :
    boundary.ι j ≫ boundaryFaceCollapse.{u} n i =
      toUnit (Δ[n] : SSet.{u}) ≫ (PointedSimplicialSet.sphere.{u} n).hom := by
  have hj : boundary.ι j = horn.ι i j hji ≫
      Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.horn_le_simplexBoundary n i) := by
    apply (cancel_mono (boundary.{u} (n + 1)).ι).mp
    simp only [boundary.ι_ι, Category.assoc, Subcomplex.homOfLE_ι, horn.ι_ι]
  rw [hj, Category.assoc, boundaryFaceCollapse_horn, comp_toUnit_assoc]

end

end SerrePositivity.KST.Spectra
