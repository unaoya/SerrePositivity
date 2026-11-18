module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.RepresentationComplex
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorNaturality

/-!
# Tate 経路の p 入力の符号付き表現複体

DAG XIII Construction 2.2.6 の p 重テンソルを、指定された置換群の作用付きで読む。
既存の Koszul 対称性と表現複体の構成を再利用し、元の全複体と全鎖写像を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {k G : Type u} [CommRing k] [Group G]

/-- 指定された置換群を通る、同じテンソル冪の実作用。 -/
def tensorPowerComplexAction (K : Complex k) (n : ℕ)
    (σ : G →* Equiv.Perm (Fin n)) : G →* End (power K n) where
  toFun g := .of (permutationAction K n (σ g)).asIso.hom
  map_one' := by apply End.ext; simp only [map_one]; rfl
  map_mul' g h := by apply End.ext; simp only [map_mul]; rfl

/-- 符号付き置換作用を保持する、全複体のテンソル冪の全関手。 -/
def tensorPowerRepresentationFunctor (n : ℕ) (σ : G →* Equiv.Perm (Fin n)) :
    Complex k ⥤ CochainComplex (Rep.{u} k G) ℤ where
  obj K := representationCochainComplex (tensorPowerComplexAction K n σ)
  map f := representationCochainMap _ _ (TensorPowers.map f n)
    (fun g => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPower_permutation_naturality k f n (σ g)).symm)
  map_id K := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply (forget₂ (Rep.{u} k G) (ModuleCat k)).map_injective
    change (TensorPowers.map (𝟙 K) n).f i = 𝟙 _
    rw [TensorPowers.map_id]
    rfl
  map_comp f h := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply (forget₂ (Rep.{u} k G) (ModuleCat k)).map_injective
    change (TensorPowers.map (f ≫ h) n).f i =
      (TensorPowers.map f n).f i ≫ (TensorPowers.map h n).f i
    rw [TensorPowers.map_comp]
    rfl

/-- 作用を忘れると元の p 重テンソルそのものに戻る指定同型。 -/
def tensorPowerRepresentationForgetIso (K : Complex k) (n : ℕ)
    (σ : G →* Equiv.Perm (Fin n)) :
    ((forget₂ (Rep.{u} k G) (ModuleCat k)).mapHomologicalComplex (.up ℤ)).obj
      ((tensorPowerRepresentationFunctor n σ).obj K) ≅ power K n :=
  representationCochainForgetIso (tensorPowerComplexAction K n σ)

end SerrePositivity.EInfinity.PowerOperation
