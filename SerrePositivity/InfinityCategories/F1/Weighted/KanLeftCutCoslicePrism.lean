module

public import SerrePositivity.InfinityCategories.F1.Weighted.KanLeftCutConeNaturality

/-!
概要：実際の weighted cone の全単体を、始点固定 coslice 値の一つの prism へ束ねる。
方針：cone の prepend 自然性を join の標準同型で移し、次数ごとの射を組む。
規約：全ての面・退化の両立を証明し、各対象の prism の存在だけで代用しない。
使われ方：共通 weighted 始域上の native pointed prism の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 実際の coslice 単体は、底・係数・時刻・変換を同時に制限する全ての面・退化と可換。 -/
lemma weightedKanLeftCutCosliceSimplex_naturality {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (σ : (nerve I) _⦋n⦌)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) :
    (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x))).map α.op
      (weightedKanLeftCutCosliceSimplex F G x σ τ s t) =
    weightedKanLeftCutCosliceSimplex F G x ((nerve I).map α.op σ)
      (simplexPrefixWeightRestriction α ≫
        Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor τ)
      ((SimplicialCategory.sHom F G).op.map α.op s) (Δ[1].map α.op t) := by
  apply Subtype.ext
  change joinMap (𝟙 Δ[0]) (stdSimplex.map α) ≫
      ((pointJoinStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
        (weightedKanLeftCutConeSimplex F G x σ τ s t)) =
    (pointJoinStdSimplexIso m).hom ≫ SSet.yonedaEquiv.symm _
  rw [← Category.assoc, joinStdSimplexIso_point_naturality, Category.assoc,
    SSet.yonedaEquiv_symm_naturality_left]
  congr 1
  exact congrArg SSet.yonedaEquiv.symm
    (weightedKanLeftCutConeSimplex_reindex F G x α σ τ s t)

/-- 左区間の実際の共同評価を覆う、全 weighted 係数と全 Hom 変換の coslice 値の prism。 -/
def weightedKanLeftCutCoslicePrism {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) :
    ((Δ[1] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj
      (weightedNerve (simplicialHomDiagram F.val x ⋙ SSet.opFunctor))) ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom F G).op ⟶
    sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x)) where
  app _ := ↾fun q => weightedKanLeftCutCosliceSimplex F G x q.1.2.down.1
    q.1.2.down.2 q.2.down q.1.1
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨t, σ, τ⟩, s⟩
    exact (weightedKanLeftCutCosliceSimplex_naturality F G x α.unop σ τ s.down t).symm

/-- 構成した全 prism の射影は、元の左区間の共同実現そのもの。 -/
lemma weightedKanLeftCutCoslicePrism_projection {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) :
    weightedKanLeftCutCoslicePrism F G x ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)) =
    ((Δ[1] ◁ (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (simplicialHomDiagram F.val x ⋙ SSet.opFunctor))) ▷
        (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom F G).op) ≫
      functorParameterizedPrism (intervalMappingUncurry
        (kanEnrichedDiagramLeftHomInterval (kanDiagramUniversalEnriched I) F G rfl rfl)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨t, σ, τ⟩, s⟩
  exact (weightedKanLeftCutCosliceSimplex_projection F G x σ τ s.down t).trans
    (kanDiagramLeftHomCutSimplex_prism F G σ s.down t).symm

end SerrePositivity.InfinityCategories
