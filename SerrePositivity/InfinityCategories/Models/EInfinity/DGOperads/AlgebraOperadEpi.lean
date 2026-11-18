module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraRestriction
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorTruncationDesc

/-!
模型。文献の定義との比較は後で
# arity ごとの全射オペラッド射に沿う代数公理の降下

概要：元の作用が全射オペラッド射で因子化すれば、同じ因子作用は商オペラッドの代数になる。
方針：全 arity の係数射の全射性で等変性・全合成則を反映する。
規約：元の底と作用因子を保持し、零入力も含む。
使われ方：零次集中 E 代数の Com 代数化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open _root_.SerrePositivity.KST.LocalizingInvariants
variable {A : Type u} [CommRing A] {P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}
  (φ : P ⟶ Q) (hφ : ∀ n, Epi (φ.map.app (_root_.SerrePositivity.FiniteBijection.of n)))
  (B : P.Algebra) (action : ∀ n, Q.arity n ⊗ power B.carrier n ⟶ B.carrier)
  (h : ∀ n, (φ.map.app (_root_.SerrePositivity.FiniteBijection.of n) ▷ power B.carrier n) ≫ action n = B.action n)

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

def ofOperadEpi : Q.Algebra where
  carrier := B.carrier
  action := action
  equivariance n σ := by
    have := hφ n
    have he := TruncationDesc.tensor_epi (φ.map.app (_root_.SerrePositivity.FiniteBijection.of n))
      (𝟙 (power B.carrier n))
    rw [tensorHom_id] at he
    apply (cancel_epi (φ.map.app (_root_.SerrePositivity.FiniteBijection.of n) ▷ power B.carrier n)).mp
    rw [whiskerRight_comp_tensorHom_assoc, ← φ.map.naturality,
      ← tensorHom_comp_whiskerRight_assoc, h]
    exact B.equivariance n σ
  unit_action := by
    rw [← φ.unit, comp_whiskerRight, Category.assoc, h]
    exact B.unit_action
  comp_action m n i := by
    have := hφ (m + 1)
    have := hφ n
    have := TruncationDesc.tensor_epi (φ.map.app (_root_.SerrePositivity.FiniteBijection.of (m + 1)))
      (φ.map.app (_root_.SerrePositivity.FiniteBijection.of n))
    have he := TruncationDesc.tensor_epi
      (φ.map.app (_root_.SerrePositivity.FiniteBijection.of (m + 1)) ⊗ₘ φ.map.app (_root_.SerrePositivity.FiniteBijection.of n))
      (𝟙 (power B.carrier (m + n)))
    rw [tensorHom_id] at he
    apply (cancel_epi ((φ.map.app (_root_.SerrePositivity.FiniteBijection.of (m + 1)) ⊗ₘ
      φ.map.app (_root_.SerrePositivity.FiniteBijection.of n)) ▷ power B.carrier (m + n))).mp
    rw [← comp_whiskerRight_assoc, ← φ.comp,
      comp_whiskerRight, Category.assoc, h, B.comp_action]
    rw [← h n, ← h (m + 1)]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionComposition_coeff (φ.map.app _) (φ.map.app _) m n i
      (action n) (action (m + 1))).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
