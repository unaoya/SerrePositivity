module
public import SerrePositivity.KST.SConstruction.SimplexHAZeroGenerator
public import SerrePositivity.KST.SConstruction.SimplexHADegreeLift

/-! # 元の HA 線形復元の零次元の実鎖射
概要：任意の HA 単体の二頂点について、零次元 cube からの元の Hom 鎖射を構成する。
方針：元の HA 辺の閉性で単位からの鎖射を作り、全次数の生成元判定で復元と照合する。
規約：元の次数線形復元の全成分と一致。使われ方：逆 Hom 鎖射の帰納の基底。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の HA 辺の閉性により、零次元の同じ線形復元を持つ実 Hom 鎖射を得る。 -/
def simplexHAZeroChainLift {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (v : Fin 1 ↪o Fin (n + 1)) (b : Fin (n + 1)) (hb : v 0 < b) :
    serreCubeComplex A 0 ⟶ homObject A D (s.obj (v 0)) (s.obj b) :=
  unitFromCycle _ (s.edgeCycle (v 0) b hb)

/-- 元の零次元の実鎖射は、同じ最高生成元上で元の HA 辺を回収する。 -/
lemma simplexHAZeroChainLift_top {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (v : Fin 1 ↪o Fin (n + 1)) (b : Fin (n + 1)) (hb : v 0 < b) :
    (simplexHAZeroChainLift A s v b hb).f 0 (serreCubeTopCell A 0) =
      s.edgeHom (v 0) b hb := by
  change (cycleFromUnit _ (unitFromCycle _ (s.edgeCycle (v 0) b hb))).val = _
  exact congrArg Subtype.val (cycleFromUnit_unitFromCycle _ _)

/-- 元の全次数の線形復元は、零次元では同じ実鎖射の各次数成分と一致する。 -/
lemma simplexHADegreeLift_zero_eq_chain {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (v : Fin 1 ↪o Fin (n + 1)) (b : Fin (n + 1)) (hb : v 0 < b) (k : ℤ) :
    simplexHADegreeLift A s.toSimplexData 0 v b hb k =
      (simplexHAZeroChainLift A s v b hb).f k := by
  apply serreCube_degree_hom_ext A 0 k
  intro i hi
  have hk : 0 = k := hi
  subst k
  exact (simplexHADegreeLift_generator A s.toSimplexData 0 v b hb 0 i rfl).trans
    ((simplexHAGeneratorValue_zero A s i v b hb).trans
      (simplexHAZeroChainLift_top A s v b hb).symm)

end SerrePositivity.KST.SConstruction
