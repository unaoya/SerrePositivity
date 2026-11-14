module

public import SerrePositivity.KST.Spectra.PointedSmallProduct
public import SerrePositivity.KST.Spectra.SmashSmallProductSimplex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.SmashProductMono

/-!
概要：固定左因子との smash から、任意の小積の各座標との smash への比較の単射性。
方針：各単体を組の代表に戻し、具体的な smash の表示で全座標を比較する。
規約：添字の有限性と Kan 性は不要。空積も含む。
使われ方：BF 1978 §2、HA §1.4.2。Sp の小積の単射構造射。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.PointedSmallProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u}

/-- smash と小積の標準比較。 -/
def smashComparison (A : PointedSimplicialSet.{u}) (X : S → PointedSimplicialSet.{u}) :
    PointedObject.smash A (obj X) ⟶ obj (fun s ↦ PointedObject.smash A (X s)) :=
  lift (fun s ↦ PointedObject.smashMap (𝟙 A) (projection X s))

/-- 具体的な小積の各単体次数の基点は基点の族。 -/
lemma basepointAt_obj (X : S → PointedSimplicialSet.{u}) (d : SimplexCategoryᵒᵖ) :
    PointedSimplicialSet.basepointAt (obj X) d =
      fun s ↦ PointedSimplicialSet.basepointAt (X s) d := rfl

/-- 全座標の smash の射影は元の smash の単体を識別する。 -/
lemma smashComparison_app_injective (A : PointedSimplicialSet.{u})
    (X : S → PointedSimplicialSet.{u}) (d : SimplexCategoryᵒᵖ) :
    Function.Injective ((smashComparison A X).right.app d) := by
  intro v w h
  obtain ⟨⟨a, b⟩, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashQuotient_app_surjective A (obj X) d v
  obtain ⟨⟨a', b'⟩, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashQuotient_app_surjective A (obj X) d w
  have he := smashSmallProduct_pack_ext (PointedSimplicialSet.basepointAt A d)
    (fun s ↦ PointedSimplicialSet.basepointAt (X s) d) a a' b b' (fun s ↦ by
      have hs := congrArg (fun z ↦ (projection
        (fun t ↦ PointedObject.smash A (X t)) s).right.app d z) h
      change ((smashComparison A X ≫ projection _ s).right.app d
        ((PointedObject.smashQuotient A (obj X)).right.app d (a, b))) =
        ((smashComparison A X ≫ projection _ s).right.app d
          ((PointedObject.smashQuotient A (obj X)).right.app d (a', b'))) at hs
      simp only [smashComparison, lift_projection] at hs
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashMap_quotient_app, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashMap_quotient_app] at hs
      have ht := congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashToSimplexModel A (X s)).right.app d z) hs
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashToSimplexModel_quotient_app, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashToSimplexModel_quotient_app] at ht
      exact ht)
  rw [← basepointAt_obj X d] at he
  have ht := congrArg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplexModelToSmashApp A (obj X) d) he
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplexModelToSmashApp_pack A (obj X) d a b).symm.trans
    (ht.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplexModelToSmashApp_pack A (obj X) d a' b'))

/-- smash から小積への標準比較の基礎単体写像はモノ射。 -/
instance smashComparison_mono (A : PointedSimplicialSet.{u})
    (X : S → PointedSimplicialSet.{u}) : Mono (smashComparison A X).right := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  exact (CategoryTheory.mono_iff_injective _).mpr (smashComparison_app_injective A X d)

end
end SerrePositivity.KST.Spectra.PointedSmallProduct
