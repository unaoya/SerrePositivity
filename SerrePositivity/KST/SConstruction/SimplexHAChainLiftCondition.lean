module
public import SerrePositivity.KST.SConstruction.SimplexHADegreeDefect

/-! # 元の全次数の HA 復元を持つ実鎖射の帰納条件
概要：元の次数線形復元を全次数で回収する実鎖射の存在と、実微分合成の差を接続する。
方針：差の零性から同じ次数射を持つ実鎖射を作り、実鎖射の回収から差の零性を得る。
規約：存在は実鎖射と回収等号を含む。使われ方：全 cube 次元の強い次元帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 全頂点列の元の HA 線形復元を、全次数で回収する実 Hom 鎖射の存在。 -/
def SimplexHAChainLiftExists {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D N) (m : ℕ) : Prop :=
  ∀ (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b),
    ∃ F : serreCubeComplex A m ⟶ homObject A D (s.obj (v 0)) (s.obj b),
      ∀ k, F.f k = simplexHADegreeLift A s m v b hb k

/-- 元の全次数の微分合成の差が零なら、同じ次数線形復元を持つ実 Hom 鎖射を作る。 -/
def simplexHAChainLiftOfDefect {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D N) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b)
    (hd : ∀ k, simplexHADegreeDefect A s m v b hb k = 0) :
    serreCubeComplex A m ⟶ homObject A D (s.obj (v 0)) (s.obj b) where
  f k := simplexHADegreeLift A s m v b hb k
  comm' k l hkl := by
    have hl : k + 1 = l := hkl
    subst l
    exact sub_eq_zero.mp (hd k)

/-- 元の実鎖射が全次数の線形復元を回収すれば、元の微分合成の差は零。 -/
lemma simplexHADegreeDefect_zero_of_chain {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D N) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b)
    (F : serreCubeComplex A m ⟶ homObject A D (s.obj (v 0)) (s.obj b))
    (hF : ∀ k, F.f k = simplexHADegreeLift A s m v b hb k) (k : ℤ) :
    simplexHADegreeDefect A s m v b hb k = 0 := by
  let K := homObject A D (s.obj (v 0)) (s.obj b)
  have h := congrArg₂ (fun (f : (serreCubeComplex A m).X k ⟶ K.X k)
    (g : (serreCubeComplex A m).X (k + 1) ⟶ K.X (k + 1)) =>
      f ≫ K.d k (k + 1) - (serreCubeComplex A m).d k (k + 1) ≫ g)
      (hF k).symm (hF (k + 1)).symm
  exact h.trans (sub_eq_zero.mpr (F.comm k (k + 1)))

end SerrePositivity.KST.SConstruction
