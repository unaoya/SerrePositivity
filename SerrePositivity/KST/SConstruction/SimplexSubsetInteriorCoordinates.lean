module
public import SerrePositivity.KST.SConstruction.SimplexSubsetEraseNormalizedFace
public import SerrePositivity.KST.SConstruction.SimplexSubsetCoordinateSign

/-! # 元の部分集合の面座標と内部頂点の同値
概要：元の濃度−2 個の面座標を、元の部分集合の厳密な内部頂点と一対一に対応させる。
方針：元の右端列挙・昇順 augmentation・削除座標の回収式を使う。
規約：元の min・max・所属を保持。使われ方：全面境界と HA の内部頂点和の添字変換。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction

/-- 元の部分集合の、元の両端の間にある所属内部頂点。 -/
abbrev SimplexSubsetInterior {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :=
  {j : Fin (n + 1) // j ∈ I ∧ I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j ∧
    j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)}

/-- 元の濃度次元の面座標に対応する、元の部分集合の内部頂点。 -/
def simplexSubsetCoordinateVertex {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (i : Fin (I.card - 2)) : Fin (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate
    (Fin.cast (necklaceInSimplexSubset_dimension.{0} I hI).symm i)).val

/-- 元の座標に対応する元の頂点は、元の部分集合に属する。 -/
lemma simplexSubsetCoordinateVertex_mem {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (i : Fin (I.card - 2)) : simplexSubsetCoordinateVertex I hI i ∈ I :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem I hI _

/-- 元の座標に対応する元の頂点は、元の両端の厳密な内部にある。 -/
lemma simplexSubsetCoordinateVertex_bounds {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (i : Fin (I.card - 2)) :
    I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < simplexSubsetCoordinateVertex I hI i ∧
      simplexSubsetCoordinateVertex I hI i < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) :=
  simplexSubsetNonjoint_bounds I hI _

/-- 元の濃度次元の面座標と、元の所属内部頂点の実際の同値。 -/
def simplexSubsetInteriorCoordinateEquiv {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) : Fin (I.card - 2) ≃ SimplexSubsetInterior I hI where
  toFun i := ⟨simplexSubsetCoordinateVertex I hI i, simplexSubsetCoordinateVertex_mem I hI i,
    simplexSubsetCoordinateVertex_bounds I hI i⟩
  invFun j := simplexSubsetEraseNormalizedCoordinate I hI j.val j.property.1
    j.property.2.1 j.property.2.2
  left_inv i := by
    apply Fin.ext
    have he := (simplexSubsetEraseCoordinate_eq_iff I hI
      (simplexSubsetCoordinateVertex I hI i) (simplexSubsetCoordinateVertex_mem I hI i)
      (simplexSubsetCoordinateVertex_bounds I hI i).1
      (simplexSubsetCoordinateVertex_bounds I hI i).2
      (Fin.cast (necklaceInSimplexSubset_dimension.{0} I hI).symm i)).mp rfl
    exact (congrArg Fin.val he).symm
  right_inv j := by
    apply Subtype.ext
    change simplexSubsetCoordinateVertex I hI
      (simplexSubsetEraseNormalizedCoordinate I hI j.val j.property.1
        j.property.2.1 j.property.2.2) = j.val
    have hc : Fin.cast (necklaceInSimplexSubset_dimension.{0} I hI).symm
        (simplexSubsetEraseNormalizedCoordinate I hI j.val j.property.1
          j.property.2.1 j.property.2.2) =
      simplexSubsetEraseCoordinate I hI j.val j.property.1 j.property.2.1 j.property.2.2 :=
      Fin.ext rfl
    exact (congrArg (fun i => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate i).val) hc).trans
        (simplexSubsetEraseCoordinate_recovery I hI j.val j.property.1
          j.property.2.1 j.property.2.2)

/-- 元の濃度座標の境界符号は、同値で対応する元の HA 頂点符号。 -/
lemma simplexSubsetCoordinateVertex_sign {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (i : Fin (I.card - 2)) :
    ((i.val : ℤ) + 1).negOnePow =
      ((I.filter (simplexSubsetCoordinateVertex I hI i < ·)).card : ℤ).negOnePow :=
  simplexSubsetCoordinate_sign I hI
    (Fin.cast (necklaceInSimplexSubset_dimension.{0} I hI).symm i)

end SerrePositivity.KST.SConstruction
