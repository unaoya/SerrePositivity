module

public import SerrePositivity.EInfinity.SimplexCuts.SignedTerms
public import SerrePositivity.EInfinity.SimplexCuts.CutNaturality

/-!
# 符号付き切断項の自然性

Berger–Fresse §2.2.6。BF の符号と、全出力次数の指定した移送を保持して自然性を示す。
5a-5a L05。前提計算は正規化生成元・純粋テンソル・次数移送の三本。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- L05 の前提計算3：既存の複体射の成分は同じ次数等式の移送と両立する。 -/
lemma component_index_naturality {K L : Complex A} (f : K ⟶ L) {i j : ℤ} (h : i = j)
    (x : K.X i) :
    f.f j ((eqToHom (congrArg K.X h)).hom x) =
      (eqToHom (congrArg L.X h)).hom (f.f i x) := by
  subst j
  rfl

lemma cutTerm_map {m q r : ℕ} {S T : SSet.{0}} (f : S ⟶ T)
    (s : Cut m q) (u : Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    (TensorPowers.map ((BarrattEccles.normalizedFunctor A).map f) r).f
      (-((m + q + 1 - r : ℕ) : ℤ)) (cutTerm A S s u x) =
        cutTerm A T s u (f.app _ x) := by
  unfold cutTerm
  rw [map_zsmul]
  congr 1
  unfold cutTensorAt
  rw [component_index_naturality, cutTensor_map]
  exact congrArg (fun t : ℕ => -(t : ℤ))
    ((degreeSum_eq_sum r (outputDegree s u)).trans (outputDegree_sum s u))

end SerrePositivity.EInfinity.SimplexCuts
