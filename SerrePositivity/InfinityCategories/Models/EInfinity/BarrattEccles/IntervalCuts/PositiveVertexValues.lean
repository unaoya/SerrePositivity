module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.BarrattEcclesVertex

/-!
模型。文献の定義との比較は後で
# 正鎖次数の頂点余作用の零性

概要：Berger–Fresse §2.2.6・§3.1 の正鎖次数演算は端点で零となる。
方針：整数余作用を頂点成分へ戻し、正次数の零性を TR 制限へ移す。
規約：全 arity、任意の係数入力。
使われ方：E-coalgebra 区間の端点の全整数余作用保存。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：χ の正鎖次数の実際の頂点余作用は零（BF §2.2.6）。
方針：面頂点を入力線形成分へ戻し、正次数の頂点成分零性を使う。
規約：全 arity・両頂点・任意の負整数次数係数。
使われ方：TR 制限後の端点の余作用保存の正鎖次数分岐。 -/
lemma cochainAction_positive_vertex (n d : ℕ) (hd : 0 < d)
    (x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X (-(d : ℤ))) (b : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n).f (-(d : ℤ))
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (-(d : ℤ)) 0 (-(d : ℤ)) (by omega)
        (x ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b))) = 0 := by
  refine (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_neg_vertex A n d x (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b))).trans ?_
  refine (congrArg (fun y => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputBilinear A n d ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).hom x) y)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector_vertex_eq A b)).trans ?_
  refine (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputBilinear_vertex A n d ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).hom x) b).trans ?_
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_eq_zero_of_positive A n d b hd, LinearMap.zero_apply]

/-- 概要：TR 制限後の E の正鎖次数の実際の頂点余作用は零（BF §3.1）。
方針：右テンソルの TR を評価し、χ の頂点零性を使う。
規約：全 arity・両頂点・任意の BE 係数。
使われ方：端点の余代数射性の負整数次数条件。 -/
lemma barrattEcclesCoaction_positive_vertex (n d : ℕ) (hd : 0 < d)
    (x : (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n).X (-(d : ℤ))) (b : Fin 2) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoalgebra A).coaction n).f (-(d : ℤ))
      (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (-(d : ℤ)) 0 (-(d : ℤ)) (by omega)
        (x ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b))) = 0 := by
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n).f (-(d : ℤ))
    (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).f (-(d : ℤ))
      (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (-(d : ℤ)) 0 (-(d : ℤ)) (by omega)
        (x ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)))) = _
  rw [SerrePositivity.DifferentialGraded.whiskerRight_apply]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_positive_vertex A n d hd _ b

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
