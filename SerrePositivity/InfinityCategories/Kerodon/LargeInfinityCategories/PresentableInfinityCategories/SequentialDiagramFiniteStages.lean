module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialEdgeDiagram

/-!
概要：可算 nerve の全射を正の有限始区間への制限で判定する。
方針：始区間の全単体表示と部分複体の被覆を使う。
規約：全次数での厳密な等式を保持する。
使われ方：指定された基底の全可算図式に沿う相対辺列の貼り合わせ。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：最初の n+1 頂点が張る全単体を可算 nerve へ含める。
方針：始区間の標準単体同型の逆を使う。
規約：全単体の射を選び、頂点族だけで代用しない。
使われ方：基底の可算図式の全有限段階への制限。 -/
def sequentialNerveInitialSimplex (n : ℕ) :
    (Δ[n] : SSet.{u}) ⟶ nerve (ULift.{u} ℕ) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStageSimplexIso n).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage n).ι

/-- 概要：有限始区間の全単体は最終面で厳密に整合する。
方針：段階の包含と標準単体同型の整合から戻す。
規約：元の可算 nerve への射の等式。
使われ方：相対全単体列の基底の整合条件。 -/
lemma sequentialNerveInitialSimplex_front (n : ℕ) :
    SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) ≫ sequentialNerveInitialSimplex.{u} (n + 1) =
      sequentialNerveInitialSimplex n := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStageSimplexIso n).hom).mp
  dsimp only [sequentialNerveInitialSimplex]
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStageSimplexIso_transition,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
  rfl

/-- 概要：可算 nerve の二つの全図式は正の有限始区間への制限で等しい。
方針：全単体がいずれかの有限始区間に属することを使う。
規約：quasicategory 性を要求しない。
使われ方：相対的に貼り合わせた図式の基底への射影の全等式。 -/
lemma sequentialNerve_hom_ext {X : SSet.{u}} {F G : nerve (ULift.{u} ℕ) ⟶ X}
    (h : ∀ n, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage (n + 1)).ι ≫ F =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage (n + 1)).ι ≫ G) : F = G := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  have hs : s ∈ (⨆ n, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage.{u} n).obj d := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.iSup_sequentialNerveStage]
    trivial
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hs
  obtain ⟨n, hn⟩ := hs
  have hn' := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone (Nat.le_succ n) d hn
  exact congrArg (fun f ↦ f.app d ⟨s, hn'⟩) (h n)

/-- 概要：可算図式の全射は正の標準単体への制限でも判定できる。
方針：各始区間の全単体同型で制限を比較する。
規約：頂点・辺の照合ではなく全単体の等式を要求する。
使われ方：基底を保つ可算全図式の構成。 -/
lemma sequentialNerve_hom_ext_initialSimplex {X : SSet.{u}}
    {F G : nerve (ULift.{u} ℕ) ⟶ X}
    (h : ∀ n, sequentialNerveInitialSimplex (n + 1) ≫ F =
      sequentialNerveInitialSimplex (n + 1) ≫ G) : F = G := by
  apply sequentialNerve_hom_ext
  intro n
  have hn := congrArg (fun f ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStageSimplexIso (n + 1)).hom ≫ f) (h n)
  simpa only [sequentialNerveInitialSimplex, Category.assoc,
    Iso.hom_inv_id_assoc] using hn

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
