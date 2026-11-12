module

public import SerrePositivity.EInfinity.PowerOperation.CyclicOrbitModel

/-!
# 正則係数の Hom とテンソル余不変の指定評価

DAG XIII Construction 2.2.6 の Tate 境界の鎖模型比較の補助。
Hom の評価と余不変の評価を明示し、同じ生成元作用を比較する。
余不変の評価は逆元を含むので、orbit 解像度では逆生成元を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
variable {k G : Type u} [CommRing k] [CommGroup G]

/-- 同じ左正則 Hom の指定評価は全係数射に自然。 -/
lemma regularHomEvaluation_natural {A B : Rep.{u} k G} (f : A ⟶ B)
    (z : Rep.leftRegular k G ⟶ A) :
    Rep.leftRegularHomEquiv B (z ≫ f) = f.hom (Rep.leftRegularHomEquiv A z) := rfl

/-- 同じ生成元作用の前合成を、係数の作用へ送る。 -/
lemma regularHomEvaluation_action (A : Rep.{u} k G) (g : G)
    (z : Rep.leftRegular k G ⟶ A) :
    Rep.leftRegularHomEquiv A ((Rep.leftRegular k G).applyAsHom g ≫ z) =
      A.ρ g (Rep.leftRegularHomEquiv A z) := by
  rw [Rep.applyAsHom_comm z g]
  exact regularHomEvaluation_natural (A.applyAsHom g) z

/-- 同じノルムの前合成を、係数のノルムへ送る。 -/
lemma regularHomEvaluation_norm [Fintype G] (A : Rep.{u} k G)
    (z : Rep.leftRegular k G ⟶ A) :
    Rep.leftRegularHomEquiv A ((Rep.leftRegular k G).norm.asHom ≫ z) =
      A.ρ.norm (Rep.leftRegularHomEquiv A z) := by
  rw [← Rep.norm_comm z]
  exact regularHomEvaluation_natural A.norm.asHom z

/-- テンソル余不変の同じ指定評価。 -/
def regularOrbitEvaluation (A : Rep.{u} k G) :
    ((Rep.coinvariantsTensor k G).obj A).obj (Rep.leftRegular k G) ≃ₗ[k] A :=
  Representation.coinvariantsTprodLeftRegularLEquiv A.ρ

lemma regularOrbitEvaluation_single (A : Rep.{u} k G) (x : A) (g : G) (r : k) :
    regularOrbitEvaluation A (Rep.coinvariantsTensorMk A (Rep.leftRegular k G)
      x (.single g r)) = r • A.ρ g⁻¹ x := by
  change Representation.ofCoinvariantsTprodLeftRegular A.ρ
    (Representation.Coinvariants.mk _ (x ⊗ₜ[k] .single g r)) = _
  exact Representation.ofCoinvariantsTprodLeftRegular_mk_tmul_single A.ρ x g r

lemma regularOrbitEvaluation_symm (A : Rep.{u} k G) (x : A) :
    (regularOrbitEvaluation A).symm x =
      Rep.coinvariantsTensorMk A (Rep.leftRegular k G) x (.single 1 1) := rfl

/-- Hom の指定評価から、同じ orbit 座標への実線形同値。 -/
def regularHomOrbitEquiv (A : Rep.{u} k G) :
    (Rep.leftRegular k G ⟶ A) ≃ₗ[k]
      ((Rep.coinvariantsTensor k G).obj A).obj (Rep.leftRegular k G) :=
  (Rep.leftRegularHomEquiv A).trans (regularOrbitEvaluation A).symm

lemma regularHomOrbitEquiv_value (A : Rep.{u} k G) (z : Rep.leftRegular k G ⟶ A) :
    regularOrbitEvaluation A (regularHomOrbitEquiv A z) = Rep.leftRegularHomEquiv A z :=
  (regularOrbitEvaluation A).apply_symm_apply _

end SerrePositivity.EInfinity.PowerOperation
