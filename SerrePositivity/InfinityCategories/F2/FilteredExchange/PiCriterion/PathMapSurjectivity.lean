module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.PiPathRelation

/-!
概要：Kan 射の固定次数での全射性は、始域の実際の path に沿って不変。
方針：path 射の自然正方形と両端点評価の全単射性を使う。
規約：標的の任意の自由 path だけから全射性を推論しない。
使われ方：元の一つの脚の像での全射性を、全空間の任意の基点へ移す。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.PiCriterion
open KST.Spectra

/-- 元の始域の同じ path の両端で、比較射の正次数の全射性は同値。 -/
lemma path_map_surjective_iff {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) (n : ℕ) (z : (KanPath.object X) _⦋0⦌)
    {x₀ x₁ : X _⦋0⦌}
    (h₀ : (KanPath.evaluation X 0).app _ z = x₀)
    (h₁ : (KanPath.evaluation X 1).app _ z = x₁) :
    Function.Surjective (KanHomotopyGroup.map (n := n) f (x := x₀) rfl) ↔
      Function.Surjective (KanHomotopyGroup.map (n := n) f (x := x₁) rfl) := by
  let p := (ihom (Δ[1] : SSet.{u})).map f
  let w := p.app (Opposite.op ⦋0⦌) z
  have hw (t : Fin 2) {x : X _⦋0⦌}
      (hx : (KanPath.evaluation X t).app _ z = x) :
      (KanPath.evaluation Y t).app _ w = f.app _ x := by
    have h := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) z)
      (path_evaluation_natural f t)
    change (KanPath.evaluation Y t).app _ w =
      f.app _ ((KanPath.evaluation X t).app _ z) at h
    simpa only [hx] using h
  have hs (t : Fin 2) {x : X _⦋0⦌}
      (hx : (KanPath.evaluation X t).app _ z = x)
      (c : KanHomotopyGroup (KanPath.object X) n z) :
      KanHomotopyGroup.map (KanPath.evaluation Y t) (hw t hx)
          (KanHomotopyGroup.map p rfl c) =
        KanHomotopyGroup.map f rfl (KanHomotopyGroup.map (KanPath.evaluation X t) hx c) :=
    KanHomotopyGroup.map_square p f (KanPath.evaluation X t) (KanPath.evaluation Y t)
      (path_evaluation_natural f t) rfl rfl hx (hw t hx) n c
  have he (t : Fin 2) {x : X _⦋0⦌}
      (hx : (KanPath.evaluation X t).app _ z = x) :
      Function.Surjective (KanHomotopyGroup.map (n := n) f (x := x) rfl) ↔
        Function.Surjective (KanHomotopyGroup.map (n := n) p (x := z) rfl) := by
    have hX := KanHomotopyGroup.map_bijective_of_piIsomorphism n (KanPath.evaluation X t)
      (KanPath.evaluation_piIsomorphism X t) hx
    have hY := KanHomotopyGroup.map_bijective_of_piIsomorphism n (KanPath.evaluation Y t)
      (KanPath.evaluation_piIsomorphism Y t) (hw t hx)
    constructor
    · intro hf a
      obtain ⟨b, hb⟩ := hf (KanHomotopyGroup.map (KanPath.evaluation Y t) (hw t hx) a)
      obtain ⟨c, hc⟩ := hX.surjective b
      refine ⟨c, hY.injective ?_⟩
      exact (hs t hx c).trans
        ((congrArg (KanHomotopyGroup.map f rfl) hc).trans hb)
    · intro hp b
      obtain ⟨a, ha⟩ := hY.surjective b
      obtain ⟨c, hc⟩ := hp a
      refine ⟨KanHomotopyGroup.map (KanPath.evaluation X t) hx c, ?_⟩
      exact (hs t hx c).symm.trans
        ((congrArg (KanHomotopyGroup.map (KanPath.evaluation Y t) (hw t hx)) hc).trans ha)
  exact (he 0 h₀).trans (he 1 h₁).symm

end SerrePositivity.InfinityCategories.F2.PiCriterion
