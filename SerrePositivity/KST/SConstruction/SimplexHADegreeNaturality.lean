module
public import SerrePositivity.KST.SConstruction.SimplexHADegreeMapRecovery

/-! # 元の HA 全生成元値と次数線形復元の後合成自然性
概要：任意の HA 成分データの生成元値と線形復元は、厳密 dg 後合成と可換。
方針：元の bead 語の生の値の自然性、次数移送、全生成元判定を合成する。
規約：任意の全次数成分を保持。使われ方：逆 Hom 射と厳密豊穣入力の自然性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の任意の HA 生成元値は、元の厳密 dg 関手による後合成を保つ。 -/
lemma simplexHAGeneratorValue_post {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {E : Type w} [DGCategory A E] (F : DGFunctor A D E)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1) ↪o Fin (n + 1))
    (b : Fin (n + 1)) (hb : v (Fin.last m) < b) :
    simplexHAGeneratorValue A (s.map F) m i v b hb =
      (F.map (s.obj (v 0)) (s.obj b)).f (serreCubeGeneratorDegree m i)
        (simplexHAGeneratorValue A s m i v b hb) := by
  unfold simplexHAGeneratorValue
  rw [simplexHABeadWordRawValue_post]
  exact (complexMap_degree_cast A (F.map _ _)
    (serreCubeGeneratorDegree_freeDimension m i).symm _).symm

/-- 元の任意の HA 次数線形復元は、元の厳密 dg 後合成と全整数次数で可換。 -/
lemma simplexHADegreeLift_post {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {E : Type w} [DGCategory A E] (F : DGFunctor A D E)
    (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last m) < b) (k : ℤ) :
    simplexHADegreeLift A (s.map F) m v b hb k =
      simplexHADegreeLift A s m v b hb k ≫ (F.map (s.obj (v 0)) (s.obj b)).f k := by
  apply serreCube_degree_hom_ext A m k
  intro i hi
  have h := congrArg (fun w => eqToHom (congrArg (fun d =>
    (homObject A E (F.obj (s.obj (v 0))) (F.obj (s.obj b))).X d) hi) w)
      (simplexHAGeneratorValue_post A s F m i v b hb)
  have ht := complexMap_degree_cast A (F.map (s.obj (v 0)) (s.obj b)) hi
    (simplexHAGeneratorValue A s m i v b hb)
  exact (simplexHADegreeLift_generator A (s.map F) m v b hb k i hi).trans
    (h.trans (ht.symm.trans
      (congrArg (fun w => (F.map (s.obj (v 0)) (s.obj b)).f k w)
        (simplexHADegreeLift_generator A s m v b hb k i hi).symm)))

end SerrePositivity.KST.SConstruction
