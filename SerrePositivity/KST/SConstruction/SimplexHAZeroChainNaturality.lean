module
public import SerrePositivity.KST.SConstruction.SimplexHAZeroChainLift

/-! # 元の零次元 HA 鎖射と厳密 dg 後合成
概要：零次元の逆 Hom 鎖射は、元の HA 単体と実 dg Hom 鎖射の後合成と厳密に可換。
方針：元の零次元生成元判定と元の HA 辺の回収式を使う。
規約：元の単体・実鎖射を保持。使われ方：逆構成の dg 自然性の零次元の基底。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の零次元の逆 Hom 鎖射は、元の厳密 dg 関手の後合成と厳密に可換。 -/
lemma simplexHAZeroChainLift_post {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    {E : Type w} [DGCategory A E] (F : DGFunctor A D E)
    (v : Fin 1 ↪o Fin (n + 1)) (b : Fin (n + 1)) (hb : v 0 < b) :
    simplexHAZeroChainLift A (s.map F) v b hb =
      simplexHAZeroChainLift A s v b hb ≫ F.map (s.obj (v 0)) (s.obj b) := by
  apply serreCube_generator_hom_ext A 0
  intro i
  change (simplexHAZeroChainLift A (s.map F) v b hb).f 0 (serreCubeTopCell A 0) =
    (F.map (s.obj (v 0)) (s.obj b)).f 0
      ((simplexHAZeroChainLift A s v b hb).f 0 (serreCubeTopCell A 0))
  rw [simplexHAZeroChainLift_top, simplexHAZeroChainLift_top]
  rfl

end SerrePositivity.KST.SConstruction
