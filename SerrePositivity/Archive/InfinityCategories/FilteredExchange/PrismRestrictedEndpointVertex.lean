module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismExtensionPullbackRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices

/-!
概要：元の実 prism を制限した後の終点の実頂点を同じ制限射で計算する。
方針：終点評価の厳密な交換式と元の具体的終点の頂点公式を合成する。
規約：元の実 prism と終点を保持。使われ方：制限後の指定比較の両端の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 制限後の実延長の終点頂点は、元の具体的終点の同じ始域制限。 -/
lemma prismRestrictedEndpoint_vertex {A C E B K D : SSet.{u}}
    (p : E ⟶ B) (d : (Δ[1] ⊗ A) ⊗ K ⟶ B) (v : A ⊗ K ⟶ E)
    (hv : v ≫ p = (prismEndpoint 0 A ▷ K) ≫ d) (s : C ⟶ A ⊗ K)
    (q : D ⟶ B) (a : A ⊗ K ⟶ D) (hj : (prismEndpoint 1 A ▷ K) ≫ d = a ≫ q)
    (W : (Δ[1] ⊗ A) ⊗ K ⟶ E) (hW : W ≫ p = d)
    (hWi : (prismEndpoint 0 A ▷ K) ≫ W = v)
    (g : A ⊗ K ⟶ pullback p q) (hg : g ≫ pullback.snd p q = a)
    (hWj : (prismEndpoint 1 A ▷ K) ≫ W = g ≫ pullback.fst p q) :
    (relativeFunctorExtensionEndpoint p (prismParameterRestriction s ≫ d)
      (prismEndpoint 0 C) (s ≫ v) (by rw [Category.assoc, hv]; rfl)
      (prismEndpoint 1 C) q (s ≫ a)
      (prismExtensionPullbackRestriction_endpoint d s q a hj)).app (Opposite.op ⦋0⦌)
      ((prismExtensionRestriction p d v hv s).app (Opposite.op ⦋0⦌)
        (relativeFunctorExtensionSpaceVertexEquiv p d (prismEndpoint 0 A ▷ K) v hv
          ⟨W, hW, hWi⟩)) =
      relativeFunctorVertex (pullback.snd p q) (s ≫ a) (s ≫ g)
        (by rw [Category.assoc, hg]) := by
  have h := congrArg (fun k => k.app (Opposite.op ⦋0⦌)
    (relativeFunctorExtensionSpaceVertexEquiv p d (prismEndpoint 0 A ▷ K) v hv ⟨W, hW, hWi⟩))
    (prismExtensionPullbackEndpoint_restrict p d v hv s q a hj)
  change (relativeFunctorOverPre (pullback.snd p q)
    (Over.homMk (U := Over.mk (s ≫ a)) (V := Over.mk a) s rfl)).app _
      ((relativeFunctorExtensionEndpoint p d (prismEndpoint 0 A ▷ K) v hv
        (prismEndpoint 1 A ▷ K) q a hj).app _
        (relativeFunctorExtensionSpaceVertexEquiv p d (prismEndpoint 0 A ▷ K) v hv
          ⟨W, hW, hWi⟩)) = _ at h
  rw [relativeFunctorExtensionEndpoint_vertex p d (prismEndpoint 0 A ▷ K) v hv
    (prismEndpoint 1 A ▷ K) q a hj W hW hWi g hg hWj] at h
  exact h.symm.trans (relativeFunctorOverPre_vertex (pullback.snd p q)
    (Over.homMk (U := Over.mk (s ≫ a)) (V := Over.mk a) s rfl) g hg)

end SerrePositivity.InfinityCategories.F2
