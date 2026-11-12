module

public import SerrePositivity.EInfinity.PowerOperation.RegularOrbitNaturality

/-!
# 逆生成元とノルムの同じ orbit 座標

DAG XIII Construction 2.2.6 の係数模型比較の補助。
同じテンソル余不変関手の実射について、作用差とノルムを評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
variable {k G : Type u} [CommRing k] [CommGroup G]

/-- 逆生成元の差は、係数の元の生成元の差へ送られる。 -/
lemma regularOrbitEvaluation_inverse_sub (A : Rep.{u} k G) (g : G)
    (x : ((Rep.coinvariantsTensor k G).obj A).obj (Rep.leftRegular k G)) :
    regularOrbitEvaluation A
      ((((Rep.coinvariantsTensor k G).obj A).map
        ((Rep.leftRegular k G).applyAsHom g⁻¹ - 𝟙 _)).hom x) =
    A.ρ g (regularOrbitEvaluation A x) - regularOrbitEvaluation A x := by
  have hi : ((((Rep.coinvariantsTensor k G).obj A).map
      (𝟙 (Rep.leftRegular k G))).hom x) = x :=
    congrArg (fun f => f.hom x)
      (((Rep.coinvariantsTensor k G).obj A).map_id (Rep.leftRegular k G))
  simp only [Functor.map_sub, ModuleCat.hom_sub, LinearMap.sub_apply, map_sub,
    regularOrbitEvaluation_action, inv_inv, hi]

/-- 正則ノルムは、同じ作用射の有限和。 -/
lemma regularNorm_eq_sum [Fintype G] :
    (Rep.leftRegular k G).norm.asHom = ∑ g : G, (Rep.leftRegular k G).applyAsHom g := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  simp only [Rep.sum_hom, Representation.IntertwiningMap.toLinearMap_sum]
  rfl

/-- 同じ orbit のノルム射は、係数のノルムへ送られる。 -/
lemma regularOrbitEvaluation_norm [Fintype G] (A : Rep.{u} k G)
    (x : ((Rep.coinvariantsTensor k G).obj A).obj (Rep.leftRegular k G)) :
    regularOrbitEvaluation A
      ((((Rep.coinvariantsTensor k G).obj A).map
        (Rep.leftRegular k G).norm.asHom).hom x) =
    A.ρ.norm (regularOrbitEvaluation A x) := by
  rw [regularNorm_eq_sum]
  simp only [Functor.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply, map_sum,
    regularOrbitEvaluation_action]
  simp only [Representation.norm, LinearMap.sum_apply]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)

end SerrePositivity.EInfinity.PowerOperation
