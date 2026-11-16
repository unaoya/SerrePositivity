module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.UniverseEdgeTransport
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
概要：小さい始域の nerve だけを持ち上げた通常図式を、同じ通常関手として読み戻す。
方針：元の頂点・辺・合成三角形を評価し、nerve の strict Segal 則で全次数を回収する。
規約：標的の対象宇宙と Hom 宇宙を同一視せず、同じ単体的写像を回収する。
使われ方：HTT Proposition 1.1.2.2 の宇宙移送、S8 の点ごとの離散性の判定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
variable {I : Type u} [SmallCategory I] {D : Type (u + 1)} [Category.{u} D]

/-- 小さい始域の同じ射列を、通常関手で送った持ち上げ nerve 図式。
HTT Proposition 1.1.2.2、既存の nerve 写像の宇宙移送の式。 -/
def smallNerveDiagram (P : I ⥤ D) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ nerve D where
  app _ := ↾fun s => s.down ⋙ P
  naturality _ _ _ := rfl

/-- 元の小さい始域の持ち上げ nerve 図式から、同じ頂点と辺を持つ通常関手を読む。
HTT Proposition 1.1.2.2、辺と合成三角形の既存の評価則。 -/
def smallNerveFunctor (r : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ nerve D) :
    I ⥤ D where
  obj i := nerveEquiv (r.app (Opposite.op ⦋0⦌) (ULift.up (ComposableArrows.mk₀ i)))
  map f := nerve.homEquiv (SSet.Edge.ofTruncated
    ((up.{u, u + 1} (nerve.edgeMk f).toTruncated).map ((truncation 2).map r)))
  map_id i := by
    rw [nerve.edgeMk_id]
    change nerve.homEquiv ((Truncated.Edge.id _).map ((truncation 2).map r)) = _
    rw [Truncated.Edge.map_id]
    exact nerve.homEquiv_id _
  map_comp f g := by
    obtain ⟨t⟩ := (nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl
    exact (nerve.homEquiv_comp
      ((upComp.{u, u + 1} t.toTruncated).map ((truncation 2).map r))).symm

/-- 読み戻した同じ通常関手の持ち上げ nerve 図式は、元の全単体的写像を回収する。
HTT Proposition 1.1.2.2、strict Segal 則と既存の全切断による等式判定。 -/
lemma smallNerveDiagram_read
    (r : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ nerve D) :
    smallNerveDiagram (smallNerveFunctor r) = r := by
  have h₁ : ∀ x, (smallNerveDiagram (smallNerveFunctor r)).app (Opposite.op ⦋1⦌) x =
      r.app (Opposite.op ⦋1⦌) x := by
    rintro ⟨x⟩
    obtain ⟨i, j, f, rfl⟩ := ComposableArrows.mk₁_surjective x
    have hm : ComposableArrows.mk₁ f ⋙ smallNerveFunctor r =
        ComposableArrows.mk₁ ((smallNerveFunctor r).map f) :=
      ComposableArrows.ext₁ rfl rfl (by simp)
    change ComposableArrows.mk₁ f ⋙ smallNerveFunctor r = _
    rw [hm]
    exact (nerve.mk₁_homEquiv_apply _).trans (ComposableArrows.mk₁_hom _)
  apply SSet.hom_ext
  intro n
  have ht : (truncation (n.unop.len + 1)).map (smallNerveDiagram (smallNerveFunctor r)) =
      (truncation (n.unop.len + 1)).map r :=
    Truncated.IsStrictSegal.hom_ext h₁
  exact NatTrans.congr_app ht (Opposite.op ⟨n.unop, Nat.le_succ _⟩)

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
