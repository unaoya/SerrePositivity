module
public import SerrePositivity.KST.SConstruction.SimplexHAInverseCellRecovery
public import SerrePositivity.KST.SConstruction.SimplexHAChainLiftTopImage
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeNormalizedComponent

/-! # 元の任意の HA 読み替え部分集合成分の復元
概要：実逆 dg 関手から抽出した native HA 成分は、元の任意の昇順列の同じ成分。
方針：元の指定次元の最高生成元像へ全 cell 回収を適用し、HA 向きの元の像を使う。
規約：元の部分集合・端点・次数を保持。使われ方：native HA へのもう一方の逆律。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の native HA 成分を、同じ指定次元の実部分集合 cell の最高生成元像で読む。 -/
lemma cubicalLambdaNativeSimplexData_hom_atDimension {N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (I : Finset (Fin (N + 1))) (a b : Fin (N + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (hk : k = 2 - (I.card : ℤ))
    (d : ℕ) (hd : d = I.card - 2) :
    (cubicalLambdaNativeSimplexData A F).hom I a b k hI ha hb hk =
      eqToHom (congrArg (fun l => (homObject A D
        (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)) (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))).X l)
        (show -(d : ℤ) = k by rw [hd]; omega))
        (serreCubeTopCellImage A _ d
          (simplexSubsetLambdaCellAtDimension A I a b hI ha hb d hd ≫
            F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))) := by
  subst d
  simpa only [simplexSubsetLambdaCellAtDimension, eqToHom_refl, Category.id_comp] using
    cubicalLambdaNativeSimplexData_hom_normalized A F I a b k hI ha hb hk

/-- 元の任意の昇順列から読む HA 成分は、実逆 dg 関手から再抽出すると厳密に戻る。 -/
lemma simplexHAInverseFunctor_native_decoded_hom {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (m : ℕ) (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1))
    (hb : v (Fin.last m) < b) :
    (cubicalLambdaNativeSimplex A (simplexHAInverseFunctor A s)).hom
        (simplexHADecodeSubset m v {b}) (v 0) b (-(m : ℤ))
        (simplexHADecodeSubset_two m v {b} (Finset.singleton_nonempty b)
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb))
        (simplexHADecodeSubset_min m v {b}
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)).symm
        (simplexHADecodeSubset_max m v {b} (Finset.singleton_nonempty b)
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)).symm (by
            have h := simplexHADecodeSubset_card m v {b}
              (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)
            simp only [Finset.card_singleton] at h
            omega) =
      s.hom (simplexHADecodeSubset m v {b}) (v 0) b (-(m : ℤ))
        (simplexHADecodeSubset_two m v {b} (Finset.singleton_nonempty b)
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb))
        (simplexHADecodeSubset_min m v {b}
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)).symm
        (simplexHADecodeSubset_max m v {b} (Finset.singleton_nonempty b)
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)).symm (by
            have h := simplexHADecodeSubset_card m v {b}
              (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)
            simp only [Finset.card_singleton] at h
            omega) := by
  have hc := simplexHADecodeSubset_card m v {b}
    (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)
  have hT : ({b} : Finset (Fin (N + 1))).Nonempty := Finset.singleton_nonempty b
  have hbound : ∀ t ∈ ({b} : Finset (Fin (N + 1))), v (Fin.last m) < t :=
    fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb
  have hd : m = (simplexHADecodeSubset m v {b}).card - 2 := by
    simp only [Finset.card_singleton] at hc
    omega
  have hn := cubicalLambdaNativeSimplexData_hom_atDimension A (simplexHAInverseFunctor A s)
    (simplexHADecodeSubset m v {b}) (v 0) b (-(m : ℤ))
    (simplexHADecodeSubset_two m v {b} hT hbound)
    (simplexHADecodeSubset_min m v {b} hbound).symm
    (simplexHADecodeSubset_max m v {b} hT hbound).symm
    (by simp only [Finset.card_singleton] at hc; omega) m hd
  simp only [eqToHom_refl] at hn
  have hr := simplexHAInverseCellRecovery A s m v b hb
  exact hn.trans ((congrArg (serreCubeTopCellImage A
    (homObject A D (s.obj (v 0)) (s.obj b)) m) hr).trans
      (simplexHAChainLift_top_image A s m v b hb))

end SerrePositivity.KST.SConstruction
