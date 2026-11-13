module

public import SerrePositivity.EInfinity.SimplexCuts.CutTensor
public import SerrePositivity.EInfinity.SimplexCuts.TensorNaturality

/-!
# 一般の切断テンソルの自然性

Berger–Fresse §2.2.6。切断の同じ面を保持し、単体集合の射を全出力へ移す。
L05 の符号付き切断項の自然性の、純粋テンソルの部分。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma cutTensor_map {m q r : ℕ} {S T : SSet.{0}} (f : S ⟶ T)
    (s : Cut m q) (u : Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    (TensorPowers.map ((BarrattEccles.normalizedFunctor A).map f) r).f
      (-(degreeSum r (outputDegree s u) : ℤ)) (cutTensor A S s u x) =
        cutTensor A T s u (f.app _ x) := by
  unfold cutTensor
  rw [tensorValue_map]
  congr 1
  funext a
  rw [gen_naturality]
  exact congrArg (gen A T (outputDegree s u a))
    (ConcreteCategory.congr_hom (f.naturality (face s u a).op) x)

end SerrePositivity.EInfinity.SimplexCuts
