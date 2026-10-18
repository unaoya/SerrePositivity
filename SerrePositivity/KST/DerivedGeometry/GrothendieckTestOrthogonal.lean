module

public import SerrePositivity.KST.DerivedGeometry.SmallMonoFamilyFactorization
public import SerrePositivity.KST.DerivedGeometry.KInjectiveLiftingCriterion
public import Mathlib.Algebra.Homology.GrothendieckAbelian

/-!
概要：Grothendieck アーベル圏の固定した試験複体の集合に直交する非有界複体を構成する。
方針：試験複体の contractible な単射の族で small object factorization を行い、持ち上げを縮約へ送る。
規約：この段階の単射の準同型性と全 acyclic 複体への直交性は別に証明する。
使われ方：Stacks 19.12.3・19.12.6、TT §3・§8、Toën §3.2 の非有界 K-injective 分解の構成部品。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits ZeroObject
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {σ : Type w} (A : σ → CochainComplex C ℤ) (M : CochainComplex C ℤ)

/--
概要：固定した試験複体の集合に対してホモトピー直交な対象への単射が存在する。
方針：試験の contractible な単射族で small object factorization を実行する。
規約：この定理だけでは単射が準同型であるとは主張しない。
使われ方：Stacks 19.12.3・19.12.6、TT §3 の小さい試験集合の超限工程。
-/
lemma exists_mono_test_homotopy_orthogonal :
    ∃ (N : CochainComplex C ℤ) (j : M ⟶ N), Mono j ∧
      ∀ (i : σ) (f : A i ⟶ N), Nonempty (Homotopy f 0) := by
  obtain ⟨N, j, p, hjp, hj, hp⟩ :=
    smallMonoFamily_exists_factorization (fun s => termInjectiveEnvelopeι (A s)) (0 : M ⟶ 0)
  have hp0 : p = (0 : N ⟶ 0) := Subsingleton.elim _ _
  rw [hp0] at hp
  refine ⟨N, j, hj, ?_⟩
  intro i f
  have : HasLiftingProperty (termInjectiveEnvelopeι (A i)) (0 : N ⟶ 0) := hp _ ⟨i⟩
  exact ⟨homotopyZero_of_envelope_lifting (A i) N f⟩

end SerrePositivity.KST.DerivedGeometry
