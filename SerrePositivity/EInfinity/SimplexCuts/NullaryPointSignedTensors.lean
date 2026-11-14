module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointGeneratorFamilies
public import SerrePositivity.EInfinity.SimplexCuts.VectorTensorTransport

/-!
# 一点削除の同じ全次数の符号付き実テンソル

Berger–Fresse §2.2.4・§2.2.6、M14 L12a、報告 §351。
元の整数符号と全指定面の生成元の族を、同じ全整数次数で比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial

/-- 一点削除の元の符号付き実テンソルは、同じ因子消去のテンソル（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_signedTensor_relabel (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word (r + 1) (m + 2)) (w : Surjection.Word r (m + 1))
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hpoint : hi s p = lo s p) (hu : ∀ j, v.val j = v.val p → j = p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i)) (x : S _⦋q⦌) (z : ℤ)
    (ht : -(vectorDegree (chains A S) r
      (fun c => ⟨outputDegree (nullaryPointEraseCut s p) w c,
        gen A S (outputDegree (nullaryPointEraseCut s p) w c)
          (S.map (face (nullaryPointEraseCut s p) w c).op x)⟩) : ℤ) = z)
    (ht' : -(vectorDegree (chains A S) (r + 0)
      (IntervalCuts.insertionFamily
        (fun a => ⟨outputDegree s v a,
          gen A S (outputDegree s v a) (S.map (face s v a).op x)⟩)
        (fun j : Fin 0 => Fin.elim0 j) k) : ℤ) = z) :
    cutSign (nullaryPointEraseCut s p) w.val •
      vectorTensorAt (chains A S) r
        (fun c => ⟨outputDegree (nullaryPointEraseCut s p) w c,
          gen A S (outputDegree (nullaryPointEraseCut s p) w c)
            (S.map (face (nullaryPointEraseCut s p) w c).op x)⟩) z ht =
      cutSign s v.val • vectorTensorAt (chains A S) (r + 0)
        (IntervalCuts.insertionFamily
          (fun a => ⟨outputDegree s v a,
            gen A S (outputDegree s v a) (S.map (face s v a).op x)⟩)
          (fun j : Fin 0 => Fin.elim0 j) k) z ht' := by
  rw [nullaryPointEraseCut_cutSign_relabel s v.val w.val p k hpoint hu hv]
  apply congrArg (fun y => cutSign s v.val • y)
  exact vectorTensorAt_congr (chains A S) r _ _ z ht ht'
    (nullaryPointEraseCut_generatorFamily_relabel A S s v w p k hp hpoint hv x)

end SerrePositivity.EInfinity.SimplexCuts
