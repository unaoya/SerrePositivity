module
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordRawValues
public import SerrePositivity.KST.SConstruction.SimplexHAReindexEvaluation

/-! # 元の生の HA 語の値と豊穣順合成
概要：向き補正前の語の連結値は、元の dg の豊穣順合成を回収する。
方針：二重の向き符号を消し、元の二次元ブロックの Koszul 比較を使う。
規約：同じ元の tensor 因子順を保持。使われ方：逆 dg Hom 射の合成保存の値の計算。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の生の HA 値は、語の右端点・自由次元の等号移送前後で異種等号を保つ。 -/
lemma simplexHABeadWordRawValue_reindex {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {a b c : Fin (n + 1)} {p q : ℕ} (hb : b = c) (hd : p = q)
    (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b p) :
    HEq (simplexHABeadWordRawValue A s (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordReindex hb hd word))
      (simplexHABeadWordRawValue A s word) := by
  cases hb
  cases hd
  rfl

/-- 元の生の HA 語の連結値は、同じ因子順の元の dg 豊穣順合成そのもの。 -/
lemma simplexHABeadWordRawValue_join {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {a b c : Fin (n + 1)} {p q : ℕ} (left : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b p)
    (right : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n b c q) :
    simplexHABeadWordRawValue A s (left.join right) =
      forward A (simplexHABeadWordRawValue A s left) (simplexHABeadWordRawValue A s right)
        (show -(p : ℤ) + -(q : ℤ) = -((p + q : ℕ) : ℤ) by omega) := by
  have cancel (M : Type u) [AddCommGroup M] (sign : ℤˣ) (x : M) :
      sign • (sign • x) = x := by
    rw [smul_smul, Int.units_mul_self, one_smul]
  have h := serreCubeOriented_compose A p q (-((p + q : ℕ) : ℤ)) (by omega)
    (simplexHABeadWordRawValue A s left) (simplexHABeadWordRawValue A s right)
  change compose A
    (serreCubeOrientationSign q • (serreCubeOrientationSign q • simplexHABeadWordValue A s right))
    (serreCubeOrientationSign p • (serreCubeOrientationSign p • simplexHABeadWordValue A s left))
    (show -(p : ℤ) + -(q : ℤ) = -((p + q : ℕ) : ℤ) by omega) = _ at h
  rw [cancel, cancel] at h
  exact (congrArg (fun x => serreCubeOrientationSign (p + q) • x) h).trans
    (cancel _ _ _)

end SerrePositivity.KST.SConstruction
