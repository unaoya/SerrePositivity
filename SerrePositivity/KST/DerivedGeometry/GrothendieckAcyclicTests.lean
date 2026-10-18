module

public import SerrePositivity.KST.DerivedGeometry.AcyclicTestsAttachment
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
概要：Grothendieck アーベル圏で試験複体の集合の全射を殺す単射準同型拡大が存在する。
方針：十分な injective と完全な coproduct を Grothendieck 性から得て実際の構成を適用する。
規約：分解の存在を構造体の未証明フィールドにしない。
使われ方：Stacks Lemma 19.12.4 (079M)、TT §3・§8、Toën §3.2 の超限工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type v} [Category.{u} C] [Abelian C] [IsGrothendieckAbelian.{u} C]
  {σ : Type u} (A : σ → CochainComplex C ℤ) (M : CochainComplex C ℤ)

/--
概要：固定した非輪状な試験複体の集合からの全射を殺す単射準同型拡大が存在する。
方針：構成済みの coproduct と押し出しに Grothendieck 性からの条件を満たして適用する。
規約：準同型性と全ての零ホモトピーを証明した存在定理。
使われ方：Stacks Lemma 19.12.4、TT §3・§8、Toën §3.2 の非有界 K-injective 分解の一工程。
-/
lemma exists_mono_quasiIso_killing_tests (hA : ∀ i, (A i).Acyclic) :
    ∃ (N : CochainComplex C ℤ) (j : M ⟶ N), Mono j ∧ QuasiIso j ∧
      ∀ (i : σ) (f : A i ⟶ M), Nonempty (Homotopy (f ≫ j) 0) := by
  refine ⟨acyclicTestsAttachment A M, acyclicTestsAttachmentι A M, inferInstance,
    acyclicTestsAttachmentι_quasiIso A M hA, ?_⟩
  intro i f
  exact ⟨acyclicTestsAttachmentNullHomotopy A M i f⟩

end SerrePositivity.KST.DerivedGeometry
