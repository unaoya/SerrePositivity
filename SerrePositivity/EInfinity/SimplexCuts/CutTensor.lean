module

public import SerrePositivity.EInfinity.SimplexCuts.Faces
public import SerrePositivity.EInfinity.SimplexCuts.HomogeneousTensor
public import SerrePositivity.EInfinity.SimplexCuts.NormalizedGenerators

/-!
# 一般の切断項と退化した切断の消滅

Berger–Fresse §2.2.6。各色の面の正規化生成元を、同じ実テンソル冪へ送る。
一つでも退化した色があれば、その因子が零となる（5a-5a L04）。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 切断の各色の実正規化生成元（BF §2.2.6）。 -/
def cutTensor {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    (power (chains A S) r).X (-(degreeSum r (outputDegree s u) : ℤ)) :=
  tensorValue (chains A S) r (outputDegree s u)
    (fun a => gen A S (outputDegree s u a) (S.map (face s u a).op x))

/-- 退化した切断項の消滅。切断全体の和を取る前の等式（BF §2.2.6）。 -/
lemma cutTensor_eq_zero {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (h : ¬Nondegenerate s u.val) (x : S _⦋q⦌) :
    cutTensor A S s u x = 0 := by
  have hn : ¬∀ a, Mono (face s u a) := fun ha => h ((faces_mono_iff s u).mp ha)
  obtain ⟨a, ha⟩ := not_forall.mp hn
  exact tensorValue_eq_zero (chains A S) r (outputDegree s u) _ a
    (gen_map_of_not_mono A S (outputDegree s u a) (face s u a) ha x)

end SerrePositivity.EInfinity.SimplexCuts
