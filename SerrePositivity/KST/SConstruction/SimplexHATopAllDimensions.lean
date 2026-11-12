module
public import SerrePositivity.KST.SConstruction.SimplexHATopCompatibility
public import SerrePositivity.KST.SConstruction.SimplexHAZeroChainLift

/-! # 元の全次元の最高生成元上の微分可換性
概要：零次元と全正次元を、元の微分の標準出力次数 −d+1 で統一する。
方針：零次元の実 HA 鎖射と、元の正次元の最高生成元比較を次数移送する。
規約：元の線形復元と実微分を保持。使われ方：全生成元の微分条件の最高生成元部分。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の次数線形復元は、同じ元の次数等号による移送を保つ。 -/
lemma simplexHADegreeLift_degree_transport {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last m) < b) {p q : ℤ} (h : p = q) (x : (serreCubeComplex A m).X p) :
    eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X h)
        (simplexHADegreeLift A s m v b hb p x) =
      simplexHADegreeLift A s m v b hb q
        (eqToHom (congrArg (fun k => (serreCubeComplex A m).X k) h) x) := by
  cases h
  rfl

/-- 零次元を含む元の全最高生成元上で、元の線形復元は標準出力次数の微分と可換。 -/
lemma simplexHADegreeLift_top_comm_all {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last m) < b) :
    (homObject A D (s.obj (v 0)) (s.obj b)).d (-(m : ℤ)) (-(m : ℤ) + 1)
        (simplexHADegreeLift A s.toSimplexData m v b hb (-(m : ℤ)) (serreCubeTopCell A m)) =
      simplexHADegreeLift A s.toSimplexData m v b hb (-(m : ℤ) + 1)
        ((serreCubeComplex A m).d (-(m : ℤ)) (-(m : ℤ) + 1) (serreCubeTopCell A m)) := by
  cases m with
  | zero =>
    rw [simplexHADegreeLift_zero_eq_chain, simplexHADegreeLift_zero_eq_chain]
    exact ConcreteCategory.congr_hom ((simplexHAZeroChainLift A s v b hb).comm 0 1)
      (serreCubeTopCell A 0)
  | succ m =>
    let K := homObject A D (s.obj (v 0)) (s.obj b)
    have hc : -(m : ℤ) = -((m + 1 : ℕ) : ℤ) + 1 := by omega
    have hd := complexDifferential_degree_transport A K rfl hc
      (simplexHADegreeLift A s.toSimplexData (m + 1) v b hb (-((m + 1 : ℕ) : ℤ))
        (serreCubeTopCell A (m + 1)))
    have h := congrArg (fun w => eqToHom (congrArg K.X hc) w)
      (simplexHADegreeLift_top_comm A s m v b hb)
    have ht := simplexHADegreeLift_degree_transport A s.toSimplexData (m + 1) v b hb hc
      ((serreCubeComplex A (m + 1)).d (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ))
        (serreCubeTopCell A (m + 1)))
    have hs := congrArg (fun w => simplexHADegreeLift A s.toSimplexData (m + 1) v b hb
      (-((m + 1 : ℕ) : ℤ) + 1) w)
      (complexDifferential_degree_transport A (serreCubeComplex A (m + 1)) rfl hc
        (serreCubeTopCell A (m + 1)))
    exact hd.trans (h.trans (ht.trans hs.symm))

end SerrePositivity.KST.SConstruction
