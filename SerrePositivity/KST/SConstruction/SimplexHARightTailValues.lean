module
public import SerrePositivity.KST.SConstruction.SimplexHARightTailPrefix
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordBoundary

/-! # 元の右側集合の復元と HA の生の値・境界値
概要：全辺付加の元の生成元語と、元の右側集合の語の両評価を同定する。
方針：始点・右端・自由次元を明示し、同じ語の異種等号を評価へ移す。
規約：境界値を微分と置き換えない。使われ方：辺付加の source 微分の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の両端点・自由次元と語が一致すれば、元の生の HA 値も同じ元。 -/
lemma simplexHABeadWordRawValue_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {a b a' b' : Fin (n + 1)} {d d' : ℕ} (ha : a = a') (hb : b = b') (hd : d = d')
    (w : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b d) (w' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a' b' d') (hw : HEq w w') :
    HEq (simplexHABeadWordRawValue A s w) (simplexHABeadWordRawValue A s w') := by
  cases ha
  cases hb
  cases hd
  cases hw
  rfl

/-- 元の両端点・自由次元と語が一致すれば、元の独立な HA 境界値も同じ元。 -/
lemma simplexHABeadWordBoundaryValue_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {a b a' b' : Fin (n + 1)} {d d' : ℕ} (ha : a = a') (hb : b = b') (hd : d = d')
    (w : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b d) (w' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a' b' d') (hw : HEq w w') :
    HEq (simplexHABeadWordBoundaryValue A s w)
      (simplexHABeadWordBoundaryValue A s w') := by
  cases ha
  cases hb
  cases hd
  cases hw
  rfl

/-- 全辺付加した元の生成元語の生の値は、元の右側集合を保つ語の同じ値。 -/
lemma simplexHARightTailPrefix_rawValue {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1) ↪o Fin (n + 1))
    (T : Finset (Fin (n + 1))) (hT : T.Nonempty) (hb : ∀ r ∈ T, v (Fin.last m) < r) :
    HEq (simplexHABeadWordRawValue A s
      (simplexHAGeneratorWord (m + (T.erase (T.max' hT)).card)
        (serreCubeGeneratorRightIndex m i (T.erase (T.max' hT)).card)
        (simplexHARightTailPrefix m v T hT hb).val (T.max' hT)
        (simplexHARightTailPrefix m v T hT hb).property))
      (simplexHABeadWordRawValue A s (simplexHABeadWordDecode m i v T hT hb)) :=
  simplexHABeadWordRawValue_heq A s (simplexHARightTailPrefix_first m v T hT hb) rfl
    (simplexHARightTailPrefix_dimension m i T hT) _ _
    (simplexHARightTailPrefix_word m i v T hT hb)

/-- 全辺付加した元の生成元語の境界値は、元の右側集合を保つ語の同じ境界値。 -/
lemma simplexHARightTailPrefix_boundaryValue {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1) ↪o Fin (n + 1))
    (T : Finset (Fin (n + 1))) (hT : T.Nonempty) (hb : ∀ r ∈ T, v (Fin.last m) < r) :
    HEq (simplexHABeadWordBoundaryValue A s
      (simplexHAGeneratorWord (m + (T.erase (T.max' hT)).card)
        (serreCubeGeneratorRightIndex m i (T.erase (T.max' hT)).card)
        (simplexHARightTailPrefix m v T hT hb).val (T.max' hT)
        (simplexHARightTailPrefix m v T hT hb).property))
      (simplexHABeadWordBoundaryValue A s (simplexHABeadWordDecode m i v T hT hb)) :=
  simplexHABeadWordBoundaryValue_heq A s (simplexHARightTailPrefix_first m v T hT hb) rfl
    (simplexHARightTailPrefix_dimension m i T hT) _ _
    (simplexHARightTailPrefix_word m i v T hT hb)

end SerrePositivity.KST.SConstruction
