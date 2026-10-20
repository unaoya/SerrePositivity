module

public import SerrePositivity.EInfinity.IntervalCuts.BarrattEcclesVertex

/-!
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

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：χ の正鎖次数の実際の頂点余作用は零（BF §2.2.6）。
方針：面頂点を入力線形成分へ戻し、正次数の頂点成分零性を使う。
規約：全 arity・両頂点・任意の負整数次数係数。
使われ方：TR 制限後の端点の余作用保存の正鎖次数分岐。 -/
lemma cochainAction_positive_vertex (n d : ℕ) (hd : 0 < d)
    (x : (Surjection.complex A n).X (-(d : ℤ))) (b : Fin 2) :
    (cochainAction A n).f (-(d : ℤ))
      (ιTensorObj (Surjection.complex A n) (interval A) (-(d : ℤ)) 0 (-(d : ℤ)) (by omega)
        (x ⊗ₜ[A] faceVector A (vertex b))) = 0 := by
  refine (cochainAction_neg_vertex A n d x (faceVector A (vertex b))).trans ?_
  refine (congrArg (fun y => vertexInputBilinear A n d ((Surjection.complexXIso A n d).hom x) y)
    (faceVector_vertex_eq A b)).trans ?_
  refine (vertexInputBilinear_vertex A n d ((Surjection.complexXIso A n d).hom x) b).trans ?_
  rw [vertexComponent_eq_zero_of_positive A n d b hd, LinearMap.zero_apply]

/-- 概要：TR 制限後の E の正鎖次数の実際の頂点余作用は零（BF §3.1）。
方針：右テンソルの TR を評価し、χ の頂点零性を使う。
規約：全 arity・両頂点・任意の BE 係数。
使われ方：端点の余代数射性の負整数次数条件。 -/
lemma barrattEcclesCoaction_positive_vertex (n d : ℕ) (hd : 0 < d)
    (x : (BarrattEccles.complex A n).X (-(d : ℤ))) (b : Fin 2) :
    ((barrattEcclesCoalgebra A).coaction n).f (-(d : ℤ))
      (ιTensorObj (BarrattEccles.complex A n) (interval A) (-(d : ℤ)) 0 (-(d : ℤ)) (by omega)
        (x ⊗ₜ[A] faceVector A (vertex b))) = 0 := by
  change (cochainAction A n).f (-(d : ℤ))
    (((TableReduction.cochainMap A n) ▷ interval A).f (-(d : ℤ))
      (ιTensorObj (BarrattEccles.complex A n) (interval A) (-(d : ℤ)) 0 (-(d : ℤ)) (by omega)
        (x ⊗ₜ[A] faceVector A (vertex b)))) = _
  rw [SerrePositivity.DifferentialGraded.whiskerRight_apply]
  exact cochainAction_positive_vertex A n d hd _ b

end SerrePositivity.EInfinity.IntervalCuts
