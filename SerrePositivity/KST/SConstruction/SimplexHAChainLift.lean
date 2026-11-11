module
public import SerrePositivity.KST.SConstruction.SimplexHAAllGeneratorCommutation
public import SerrePositivity.KST.SConstruction.SerreCubeChainLift

/-! # 元の native HA 単体の全次数の標準 Hom 鎖射復元
概要：元の全生成元値を持つ同じ Hom 鎖射を、標準の全生成元鎖射復元から構成する。
方針：証明済みの全生成元の実微分可換性を、元の次数移送付き生成元値へ適用する。
規約：鎖射性の追加仮定を置かない。使われ方：native HA 単体からの逆 dg Hom 射。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の native HA 単体から、元の全生成元値を持つ実 Hom 鎖射を無条件に復元する。 -/
def simplexHAChainLift {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b) :
    serreCubeComplex A m ⟶ homObject A D (s.obj (v 0)) (s.obj b) :=
  serreCubeChainLift A m (homObject A D (s.obj (v 0)) (s.obj b))
    (fun _ i hi => eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X hi)
      (simplexHAGeneratorValue A s.toSimplexData m i v b hb))
    (fun k i hi => (congrArg (fun x => (homObject A D (s.obj (v 0)) (s.obj b)).d k (k + 1) x)
      (simplexHADegreeLift_generator A s.toSimplexData m v b hb k i hi)).symm.trans
        (simplexHADegreeLift_generator_comm A s m i v b hb k hi))

/-- 元の実 Hom 鎖射の全整数次数成分は、元の同じ次数線形復元そのもの。 -/
lemma simplexHAChainLift_f {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b) (k : ℤ) :
    (simplexHAChainLift A s m v b hb).f k = simplexHADegreeLift A s.toSimplexData m v b hb k := rfl

/-- 元の実 Hom 鎖射は、元の全生成元の指定次数移送の HA 値を回収する。 -/
lemma simplexHAChainLift_generator {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b)
    (k : ℤ) (i : SerreCubeGeneratorIndex m) (hi : serreCubeGeneratorDegree m i = k) :
    (simplexHAChainLift A s m v b hb).f k
      (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi) (serreCubeGenerator A m i)) =
      eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X hi)
        (simplexHAGeneratorValue A s.toSimplexData m i v b hb) :=
  simplexHADegreeLift_generator A s.toSimplexData m v b hb k i hi

end SerrePositivity.KST.SConstruction
