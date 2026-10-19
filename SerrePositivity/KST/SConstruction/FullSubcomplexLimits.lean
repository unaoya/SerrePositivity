module
public import SerrePositivity.KST.SConstruction.FullSubcomplexColimits
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitCriterion

/-! # 全部分複体による極限の反映
概要：周囲で極限となる全部分複体内の錐は内部でも極限。
方針：相対終点境界充填を、全頂点を含む境界に沿って持ち上げる。
規約：周囲だけ quasicategory。使われ方：相対 cofiber 図式の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全境界の持ち上げがある単射な表示を通じて相対終点境界充填を反映する。 -/
lemma terminalBoundaryLifting_reflect_of_boundary_lifting {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B') (i : E ⟶ E') (j : B ⟶ B') [Mono j]
    (h : i ≫ q = p ≫ j)
    (hi : ∀ n : ℕ, HasLiftingProperty (boundary (n + 1)).ι i)
    {x : E _⦋0⦌} (hx : TerminalBoundaryLifting q (i.app (Opposite.op ⦋0⦌) x)) :
    TerminalBoundaryLifting p x := by
  intro n a b ha sq
  have hf : boundaryVertex n (Fin.last (n + 1)) ≫ (a ≫ i) =
      SSet.yonedaEquiv.symm (i.app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, ha, SSet.yonedaEquiv_symm_comp]
  have cs : CommSq (a ≫ i) (boundary (n + 1)).ι q (b ≫ j) := by
    constructor
    rw [Category.assoc, h, ← Category.assoc, sq.w, Category.assoc]
  obtain ⟨F, hF, hFq⟩ := hx n _ _ hf cs
  have := hi n
  have cs' : CommSq a (boundary (n + 1)).ι i F := ⟨hF.symm⟩
  refine ⟨cs'.lift, cs'.fac_left, ?_⟩
  apply (cancel_mono j).1
  rw [Category.assoc, ← h, ← Category.assoc, cs'.fac_right, hFq]

/-- 全部分複体の錐の周囲での極限性を内部へ反映する。 -/
lemma isLimitCone_fullSubcomplex_of_ambient {K X : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop) {p : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})}
    (c : JoinCone p)
    (hc : IsLimitCone (mapJoinCone (fullSubcomplexOnVertices X P).ι c)) : IsLimitCone c := by
  apply isLimitCone_of_terminalBoundaryLifting_coneRestriction c
  apply terminalBoundaryLifting_reflect_of_boundary_lifting
    (coneRestriction K (fullSubcomplexOnVertices X P : SSet.{u}))
    (coneRestriction K X) ((ihom (join (Δ[0] : SSet.{u}) K)).map
      (fullSubcomplexOnVertices X P).ι) ((ihom K).map (fullSubcomplexOnVertices X P).ι)
  · exact (pre (joinInr (Δ[0] : SSet.{u}) K)).naturality _
  · intro n
    exact ihom_fullSubcomplex_hasLiftingProperty_of_vertexSurjective _ P _
      (boundary_vertex_surjective n)
  · exact terminalBoundaryLifting_coneRestriction_of_isLimitCone _ hc

/-- 全部分複体内の四角形の周囲での引き戻し性を内部へ反映する。 -/
lemma isPullbackSquare_fullSubcomplex_of_ambient {X : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop)
    (G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (fullSubcomplexOnVertices X P : SSet.{u}))
    (hG : IsPullbackSquare (G ≫ (fullSubcomplexOnVertices X P).ι)) : IsPullbackSquare G := by
  apply isLimitCone_fullSubcomplex_of_ambient P (pullbackCone G)
  exact hG

end SerrePositivity.KST.SConstruction
