module
public import SerrePositivity.KST.SConstruction.SimplexHABeadTailValues
public import SerrePositivity.KST.SConstruction.SimplexHAGeneratorValues

/-! # 元の零次元生成元に指定した HA 値の計算
概要：零次元の生成元読み替えは、同じ二端点の元の HA 辺を回収する。
方針：読み替えの零段と、元の右端一点の bead の評価を計算する。
規約：任意の厳密に順序付けられた二頂点。使われ方：逆 Hom 鎖射の零次元の基底。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の零次元生成元の語の評価は、同じ端点の元の HA 辺。 -/
lemma simplexHAGeneratorWord_zero_value {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (i : SerreCubeGeneratorIndex 0) (v : Fin 1 ↪o Fin (n + 1))
    (b : Fin (n + 1)) (hb : v 0 < b) :
    simplexHABeadWordValue A s.toSimplexData (simplexHAGeneratorWord 0 i v b hb) =
      s.edgeHom (v 0) b hb := by
  change simplexHABeadWordValue A s.toSimplexData
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail {b} (Finset.singleton_nonempty b) (v 0) (by
      intro t ht
      simpa only [Finset.mem_singleton.mp ht] using hb)) = _
  have hI : 2 ≤ ({v 0, b} : Finset (Fin (n + 1))).card := by simp [ne_of_lt hb]
  have ha : v 0 = ({v 0, b} : Finset (Fin (n + 1))).min'
      (Finset.card_pos.mp (by omega)) := by
    symm
    exact (Finset.min'_eq_iff _ _ _).mpr ⟨by simp, by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact le_rfl
      · exact hb.le⟩
  have hmax : b = ({v 0, b} : Finset (Fin (n + 1))).max'
      (Finset.card_pos.mp (by omega)) := by
    symm
    exact (Finset.max'_eq_iff _ _ _).mpr ⟨by simp, by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hb.le
      · exact le_rfl⟩
  have h := simplexHABeadTail_value A s.toSimplexData {b} (Finset.singleton_nonempty b) (v 0)
    (by intro t ht; simpa only [Finset.mem_singleton.mp ht] using hb) hI ha
    (by simpa only [Finset.max'_singleton] using hmax)
  exact h.trans (by rfl)

/-- 元の零次元の向き補正前の HA 生成元値も、元の同じ HA 辺。 -/
lemma simplexHAGeneratorValue_zero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (i : SerreCubeGeneratorIndex 0) (v : Fin 1 ↪o Fin (n + 1))
    (b : Fin (n + 1)) (hb : v 0 < b) :
    simplexHAGeneratorValue A s.toSimplexData 0 i v b hb = s.edgeHom (v 0) b hb := by
  change serreCubeOrientationSign 0 •
    simplexHABeadWordValue A s.toSimplexData (simplexHAGeneratorWord 0 i v b hb) = _
  rw [serreCubeOrientationSign_zero, one_smul]
  exact simplexHAGeneratorWord_zero_value A s i v b hb

end SerrePositivity.KST.SConstruction
