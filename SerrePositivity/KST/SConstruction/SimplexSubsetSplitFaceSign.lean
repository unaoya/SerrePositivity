module
public import SerrePositivity.KST.SConstruction.SimplexSubsetCoordinateSign
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitOneFace

/-! # 元の分割標準一面の座標と HA 符号
概要：元の二 bead の共有座標に一を加えた数を、右 bead 長・HA の右側頂点数と同定。
方針：元の一 bead の右端座標と共有頂点の回収、元の右フィルターの濃度を使う。
規約：元の一面因子分解で使う座標そのもの。使われ方：HA 方程式の非線形項の符号。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction

/-- 元の二 bead の共有座標に一を加えると、元の右 bead の長さ。 -/
lemma necklaceWedgeBeadMissingCoordinate_val (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    (necklaceRefinementMissingCoordinate
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} p) (necklaceBead q))
      (necklaceWedgeBeadSeam p q hp hq)).val + 1 = q := by
  let v := necklaceWedgeBeadSeam p q hp hq
  let i := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (p + q)).nonjointCoordinate.symm v
  have hc := necklaceSingleCoordinate_val (p + q) i
  have he := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (p + q)).nonjointCoordinate.apply_symm_apply v
  have hv : ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (p + q)).nonjointCoordinate i).val.val = p :=
    congrArg (fun w : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (p + q)).NonjointVertex => w.val.val) he
  change i.val + 1 = q
  omega

/-- 元の実分割標準一面の座標に一を加えると、元の切断点より右の頂点数になる。 -/
lemma simplexSubsetSplit_face_coordinate {n : ℕ} (I : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    (necklaceRefinementMissingCoordinate
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} ((I.filter (· ≤ j)).card - 1))
        (necklaceBead ((I.filter (j ≤ ·)).card - 1)))
      (necklaceWedgeBeadSeam ((I.filter (· ≤ j)).card - 1)
        ((I.filter (j ≤ ·)).card - 1) (by omega) (by omega))).val + 1 =
        (I.filter (j < ·)).card := by
  have hc := necklaceWedgeBeadMissingCoordinate_val.{u}
    ((I.filter (· ≤ j)).card - 1) ((I.filter (j ≤ ·)).card - 1) (by omega) (by omega)
  have hr := simplexSubsetStrictRight_card I j hj
  omega

/-- 元の実分割一面の境界符号は、元の HA の切断点より右の頂点数の符号そのもの。 -/
lemma simplexSubsetSplit_face_sign {n : ℕ} (I : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    (((necklaceRefinementMissingCoordinate
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} ((I.filter (· ≤ j)).card - 1))
        (necklaceBead ((I.filter (j ≤ ·)).card - 1)))
      (necklaceWedgeBeadSeam ((I.filter (· ≤ j)).card - 1)
        ((I.filter (j ≤ ·)).card - 1) (by omega) (by omega))).val + 1 : ℕ) : ℤ).negOnePow =
        ((I.filter (j < ·)).card : ℤ).negOnePow :=
  congrArg (fun k : ℕ => (k : ℤ).negOnePow)
    (simplexSubsetSplit_face_coordinate.{u} I j hj hL hR)

end SerrePositivity.KST.SConstruction
