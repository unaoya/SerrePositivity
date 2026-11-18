module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryPointFaceFamilies
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NormalizedGenerators

/-!
模型。文献の定義との比較は後で
# 一点削除の元の指定面による正規化生成元の全族

Berger–Fresse §2.2.6、M14 L12a、報告 §351。
同じSigma型の指定面から来る生成元を、元の全出力順序で比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open scoped _root_.Simplicial

/-- 一点削除の前後で、元の指定面による同じ生成元の全族が一致（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_generatorFamily_relabel (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (r + 1) (m + 2)) (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1))
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hpoint : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i)) (x : S _⦋q⦌) :
    (fun c : Fin r =>
      (⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) w c,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) w c)
          (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) w c).op x)⟩ :
        Σ d : ℕ, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X (-(d : ℤ)))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily
        (fun a => ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a,
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s v a).op x)⟩)
        (fun j : Fin 0 => Fin.elim0 j) k := by
  let Φ (F : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)) :
      Σ d : ℕ, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X (-(d : ℤ)) :=
    ⟨F.1, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S F.1 (S.map (SimplexCategory.mkHom F.2).op x)⟩
  funext c
  have H := congrArg Φ
    (congrFun (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut_faceFamily_relabel s v w p k hp hpoint hv) c)
  refine H.trans ?_
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily
  cases he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv r 0 k c with
  | inl a => rfl
  | inr a => exact Fin.elim0 a

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
