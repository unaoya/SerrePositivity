module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NormalizedGenerators
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HomogeneousTensor

/-!
模型。文献の定義との比較は後で
# 同じ指定面の生成元と次数移送

Berger–Fresse §2.2.6–7、M14 L09a。
既存の生成元と純粋テンソルを、同じ次数の等式に沿って移す法則。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C158：指定面の始域を移すと、同じ生成元は逆向きの次数移送で読める。 -/
lemma gen_cast_source (S : SSet.{0}) {n n' q : ℕ} (h : n = n')
    (f : (⦋n'⦌ : SimplexCategory) ⟶ ⦋q⦌) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S n (S.map (eqToHom (congrArg SimplexCategory.mk h) ≫ f).op x) =
      (eqToHom (congrArg (fun t : ℤ => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X t)
        (congrArg (fun k : ℕ => -(k : ℤ)) h.symm))).hom
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S n' (S.map f.op x)) := by
  subst n'
  simp

/-- C159：次数の族と各因子を同じ等式で移すと、純粋テンソル全体もその移送になる。 -/
lemma tensorValue_congr_degree (K : Complex A) (n : ℕ) (d e : Fin n → ℕ)
    (h : d = e) (v : ∀ i, K.X (-(d i : ℤ))) (w : ∀ i, K.X (-(e i : ℤ)))
    (hv : ∀ i, (eqToHom (congrArg (fun t : ℤ => K.X t)
      (congrArg (fun k : ℕ => -(k : ℤ)) (congrFun h i)))).hom (v i) = w i) :
    (eqToHom (congrArg (fun t : ℤ => (power K n).X t)
      (congrArg (fun k : ℕ => -(k : ℤ)) (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n) h)))).hom
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K n d v) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K n e w := by
  subst e
  have he : v = w := by
    funext i
    simpa only [eqToHom_refl, ModuleCat.id_apply] using hv i
  subst w
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
