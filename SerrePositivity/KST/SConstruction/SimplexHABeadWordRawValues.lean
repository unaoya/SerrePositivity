module
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordRecovery

/-! # 元の bead 連結語の向き補正前の HA 値
概要：HA の連結語値から、元の端点・辺 tensor 生成元へ使う向き補正前の値を得る。
方針：元の全自由次元の向き符号をもう一度掛け、実鎖射の生の最高生成元像を回収する。
規約：符号は元の同じ cube の次元。使われ方：次数線形復元への生成元値の入力。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の HA 連結語値の向きを戻し、元の生の tensor 生成元に割り当てる値。 -/
def simplexHABeadWordRawValue {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {a b : Fin (n + 1)} {d : ℕ} (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b d) :
    GradedHom A (s.obj a) (s.obj b) (-(d : ℤ)) :=
  serreCubeOrientationSign d • simplexHABeadWordValue A s word

/-- 元の生の連結語値も、元の厳密 dg 関手による後合成と厳密に可換。 -/
lemma simplexHABeadWordRawValue_post {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {E : Type w} [DGCategory A E] (F : DGFunctor A D E)
    {a b : Fin (n + 1)} {d : ℕ} (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b d) :
    simplexHABeadWordRawValue A (s.map F) word =
      (F.map (s.obj a) (s.obj b)).f (-(d : ℤ)) (simplexHABeadWordRawValue A s word) := by
  unfold simplexHABeadWordRawValue
  rw [simplexHABeadWordValue_post]
  have hm (V W : ModuleCat.{u} A) (f : V ⟶ W) (s : ℤˣ) (x : V) :
      f (s • x) = s • f x := by
    simp only [Units.smul_def, map_zsmul]
  exact (hm _ _ ((F.map (s.obj a) (s.obj b)).f (-(d : ℤ)))
    (serreCubeOrientationSign d) (simplexHABeadWordValue A s word)).symm

/-- 元の生の連結語値は、元の実鎖射の向き補正前の最高生成元像を回収する。 -/
lemma simplexHABeadWordRawValue_recovery {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    {a b : Fin (n + 1)} {d : ℕ} (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b d) :
    simplexHABeadWordRawValue A (cubicalLambdaNativeSimplexData A F) word =
      (simplexHABeadWordCell A word ≫ F.map _ _).f (-(d : ℤ))
        (serreCubeTopCell A d) := by
  unfold simplexHABeadWordRawValue
  rw [simplexHABeadWordValue_recovery]
  change serreCubeOrientationSign d •
    (simplexHABeadWordCell A word ≫ F.map _ _).f (-(d : ℤ))
      (serreCubeOrientationSign d • serreCubeTopCell A d) = _
  have hm (V W : ModuleCat.{u} A) (f : V ⟶ W) (s : ℤˣ) (x : V) :
      f (s • x) = s • f x := by
    simp only [Units.smul_def, map_zsmul]
  rw [hm, smul_smul, Int.units_mul_self, one_smul]

end SerrePositivity.KST.SConstruction
