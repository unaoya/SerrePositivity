module

public import SerrePositivity.KST.DerivedGeometry.SmallMonoQuasiIsoFactorization
public import SerrePositivity.KST.DerivedGeometry.GrothendieckTestOrthogonal

/-!
概要：固定した acyclic 試験複体の集合に直交する対象への非有界単射準同型を構成する。
方針：試験の contractible な単射族の small object factorization で左射の準同型性も証明する。
規約：全ての acyclic 複体への直交性と各項 injectivity は別の判定工程。
使われ方：Stacks 19.12.3・19.12.6、TT §3・§8、Toën §3.2 の非有界 K-injective 分解。
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
概要：固定した非輪状な試験複体の集合に直交する対象への単射準同型が存在する。
方針：実際の small object factorization と縮約による零ホモトピーを組み合わせる。
規約：試験集合だけの判定と全 K-injective 性を区別する。
使われ方：Stacks 19.12.3・19.12.6、TT §3・§8、Toën §3.2 の非有界分解の超限工程。
-/
lemma exists_mono_quasiIso_test_homotopy_orthogonal (hA : ∀ i, (A i).Acyclic) :
    ∃ (N : CochainComplex C ℤ) (j : M ⟶ N), Mono j ∧ QuasiIso j ∧
      ∀ (i : σ) (f : A i ⟶ N), Nonempty (Homotopy f 0) := by
  have hi : ∀ i, QuasiIso (termInjectiveEnvelopeι (A i)) := fun i =>
    quasiIso_of_acyclic (A i) _ _ (hA i) (adjacentBiproductComplex_acyclic _)
  obtain ⟨N, j, p, hjp, hj, hqj, hp⟩ :=
    smallMonoQuasiIsoFamily_exists_factorization (fun s => termInjectiveEnvelopeι (A s)) hi (0 : M ⟶ 0)
  have hp0 : p = (0 : N ⟶ 0) := Subsingleton.elim _ _
  rw [hp0] at hp
  refine ⟨N, j, hj, hqj, ?_⟩
  intro i f
  have : HasLiftingProperty (termInjectiveEnvelopeι (A i)) (0 : N ⟶ 0) := hp _ ⟨i⟩
  exact ⟨homotopyZero_of_envelope_lifting (A i) N f⟩

end SerrePositivity.KST.DerivedGeometry
