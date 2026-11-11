module
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordDecode
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordRawValues

/-! # 元の全 tensor 生成元への native HA 値
概要：同じ元の零・一端点・辺を bead 連結語へ読み、全生成元に HA 値を割り当てる。
方針：右端の未処理集合を一点に取り、元の自由次元の向きを戻して次数を移す。
規約：端点と元の生成元次数を保持。使われ方：逆 Hom 射の全次数線形復元。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

/-- 元の全 tensor 生成元を、同じ端点・自由次元の部分集合 bead 連結語へ読む。 -/
def simplexHAGeneratorWord {n : ℕ} (m : ℕ) (i : SerreCubeGeneratorIndex m)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1)) (hb : v (Fin.last m) < b) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n (v 0) b (serreCubeGeneratorFreeDimension m i) := by
  have hbs : ∀ t ∈ ({b} : Finset (Fin (n + 1))), v (Fin.last m) < t := by
    intro t ht
    simpa only [Finset.mem_singleton.mp ht] using hb
  simpa only [Finset.card_singleton, Nat.add_sub_cancel, Finset.max'_singleton] using
    simplexHABeadWordDecode m i v {b} (Finset.singleton_nonempty b) hbs

variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の全 tensor 生成元に割り当てる、元の端点と生成元次数を持つ native HA 値。 -/
def simplexHAGeneratorValue {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1) ↪o Fin (n + 1))
    (b : Fin (n + 1)) (hb : v (Fin.last m) < b) :
    GradedHom A (s.obj (v 0)) (s.obj b) (serreCubeGeneratorDegree m i) :=
  eqToHom (congrArg (fun k => (homObject A D (s.obj (v 0)) (s.obj b)).X k)
    (serreCubeGeneratorDegree_freeDimension m i).symm)
    (simplexHABeadWordRawValue A s (simplexHAGeneratorWord m i v b hb))

/-- 元の実 dg 関手からの HA 生成元値は、同じ連結語の生の最高生成元像の次数移送。 -/
lemma simplexHAGeneratorValue_recovery {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1) ↪o Fin (n + 1))
    (b : Fin (n + 1)) (hb : v (Fin.last m) < b) :
    simplexHAGeneratorValue A (cubicalLambdaNativeSimplexData A F) m i v b hb =
      eqToHom (congrArg (fun k => (homObject A D
        (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0))) (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))).X k)
        (serreCubeGeneratorDegree_freeDimension m i).symm)
        ((simplexHABeadWordCell A (simplexHAGeneratorWord m i v b hb) ≫ F.map _ _).f
          (-(serreCubeGeneratorFreeDimension m i : ℤ))
          (serreCubeTopCell A (serreCubeGeneratorFreeDimension m i))) := by
  unfold simplexHAGeneratorValue
  rw [simplexHABeadWordRawValue_recovery]
  rfl

end SerrePositivity.KST.SConstruction
