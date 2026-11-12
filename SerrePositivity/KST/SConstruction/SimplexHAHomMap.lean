module
public import SerrePositivity.KST.SConstruction.SimplexHAIntervalHomMap
public import SerrePositivity.KST.SConstruction.SimplexLambdaDiagonalMap
public import SerrePositivity.KST.SConstruction.SimplexIntervalReverseHom

/-! # 元の native HA 単体による全頂点間の Λ Hom 鎖射
概要：元の厳密区間・対角・逆向きの全 Hom に、同じ HA データから実鎖射を与える。
方針：厳密区間の全次数復元、対角の増大と単位、逆向きの実零 Hom を使う。
規約：元の全 Hom と全頂点を保持。使われ方：単位・合成を持つ実逆 dg 関手の Hom 族。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の native HA 単体から、元の標準単体の全頂点間の Λ Hom の実鎖射を得る。 -/
def simplexHAHomMap {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (a b : Fin (N + 1)) :
    homObject A (CubicalLambda A (Δ[N] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) ⟶ homObject A D (s.obj a) (s.obj b) :=
  if h : a = b then by
    subst b
    exact simplexLambdaDiagonalMap A a (s.obj a)
  else if hab : a < b then simplexHAIntervalHomMap A s a b hab else 0

/-- 元の全 Hom 族の対角分岐は、元の増大・単位による実鎖射。 -/
lemma simplexHAHomMap_self {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (a : Fin (N + 1)) :
    simplexHAHomMap A s a a = simplexLambdaDiagonalMap A a (s.obj a) := by
  simp only [simplexHAHomMap, dite_true]

/-- 元の全 Hom 族の厳密区間分岐は、元の全内部頂点を持つ実 Hom 鎖射。 -/
lemma simplexHAHomMap_of_lt {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b : Fin (N + 1)) (hab : a < b) :
    simplexHAHomMap A s a b = simplexHAIntervalHomMap A s a b hab := by
  simp only [simplexHAHomMap, dite_eq_right (ne_of_lt hab), dite_eq_left hab]

/-- 元の全 Hom 族の逆向き分岐は、元の実零 Hom からの零鎖射。 -/
lemma simplexHAHomMap_of_gt {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b : Fin (N + 1)) (hba : b < a) : simplexHAHomMap A s a b = 0 := by
  simp only [simplexHAHomMap, dite_eq_right (ne_of_gt hba), dite_eq_right (not_lt_of_ge hba.le)]

/-- 元の全 Hom 族は、元の各頂点の実単位を保持する。 -/
lemma simplexHAHomMap_id {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (a : Fin (N + 1)) :
    eId (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) ≫
      simplexHAHomMap A s a a = eId (Complex A) (s.obj a) := by
  rw [simplexHAHomMap_self]
  exact simplexLambdaDiagonalMap_id A a (s.obj a)

/-- 元の全頂点間の Hom 族は、元の厳密 dg 関手による後合成と可換。 -/
lemma simplexHAHomMap_post {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    {E : Type w} [DGCategory A E] (F : DGFunctor A D E) (a b : Fin (N + 1)) :
    simplexHAHomMap A (s.map F) a b = simplexHAHomMap A s a b ≫ F.map (s.obj a) (s.obj b) := by
  by_cases h : a = b
  · subst b
    rw [simplexHAHomMap_self, simplexHAHomMap_self]
    exact simplexLambdaDiagonalMap_post A a (s.obj a) F
  · by_cases hab : a < b
    · rw [simplexHAHomMap_of_lt A (s.map F) a b hab, simplexHAHomMap_of_lt A s a b hab]
      exact simplexHAIntervalHomMap_post A s F a b hab
    · have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm h)
      rw [simplexHAHomMap_of_gt A (s.map F) a b hba, simplexHAHomMap_of_gt A s a b hba]
      exact (Limits.zero_comp).symm

end SerrePositivity.KST.SConstruction
