module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointFaceFamilies
public import SerrePositivity.EInfinity.SimplexCuts.NormalizedGenerators

/-!
# 一点削除の元の指定面による正規化生成元の全族

Berger–Fresse §2.2.6、M14 L12a、報告 §351。
同じSigma型の指定面から来る生成元を、元の全出力順序で比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- 一点削除の前後で、元の指定面による同じ生成元の全族が一致（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_generatorFamily_relabel (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word (r + 1) (m + 2)) (w : Surjection.Word r (m + 1))
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hpoint : hi s p = lo s p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i)) (x : S _⦋q⦌) :
    (fun c : Fin r =>
      (⟨outputDegree (nullaryPointEraseCut s p) w c,
        gen A S (outputDegree (nullaryPointEraseCut s p) w c)
          (S.map (face (nullaryPointEraseCut s p) w c).op x)⟩ :
        Σ d : ℕ, (chains A S).X (-(d : ℤ)))) =
      IntervalCuts.insertionFamily
        (fun a => ⟨outputDegree s v a,
          gen A S (outputDegree s v a) (S.map (face s v a).op x)⟩)
        (fun j : Fin 0 => Fin.elim0 j) k := by
  let Φ (F : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)) :
      Σ d : ℕ, (chains A S).X (-(d : ℤ)) :=
    ⟨F.1, gen A S F.1 (S.map (SimplexCategory.mkHom F.2).op x)⟩
  funext c
  have H := congrArg Φ
    (congrFun (nullaryPointEraseCut_faceFamily_relabel s v w p k hp hpoint hv) c)
  refine H.trans ?_
  unfold IntervalCuts.insertionFamily
  cases he : operadInsertionEquiv r 0 k c with
  | inl a => rfl
  | inr a => exact Fin.elim0 a

end SerrePositivity.EInfinity.SimplexCuts
