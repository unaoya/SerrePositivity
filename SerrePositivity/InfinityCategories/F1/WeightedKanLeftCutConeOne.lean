module

public import SerrePositivity.InfinityCategories.F1.WeightedKanLeftCutConeZero
public import SerrePositivity.InfinityCategories.F1.WeightedKanHomCompositeDiagram

/-!
概要：左切断の時刻一で、実際の weighted Hom 作用後の元の cone を回収する。
方針：時刻一の切断係数を、元の全変換で評価した合成係数へ厳密に戻す。
規約：合成係数の自然性は元の weighted nerve の作用から構成済み。
使われ方：共通 weighted 始域上の pointed prism の終点の固定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 全頂点が時刻一なら、切断 cone は元の weighted Hom 作用後の cone そのもの。 -/
lemma weightedKanLeftCutConeSimplex_one {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (ht : ∀ j, (stdSimplex.objEquiv t).toOrderHom j = 1) :
    weightedKanLeftCutConeSimplex F G x σ τ s t =
      weightedConeSimplex G.val x (weightedKanHomCompositeDiagram F G x σ τ s) := by
  refine coherentConeSimplexOfHead_eq_weighted G.val x σ
    (weightedKanHomCompositeDiagram F G x σ τ s) _
    (weightedKanLeftCutConeHead F G x σ τ s t)
    (fun j => kanDiagramLeftHomCutSimplex_obj_one F G σ s t j (ht j)) (fun j => ?_)
    (fun i j hij => weightedKanLeftCutTail_one F G σ s t i j hij (ht i) (ht j))
  change weightedKanLeftCutHead F G x σ τ s t j ≫
    eqToHom (congrArg (SimplicialCategory.sHom x)
      (kanDiagramLeftHomCutSimplex_obj_one F G σ s t j (ht j))) = _
  rw [weightedKanLeftCutHead_one F G x σ τ s t j (ht j)]
  change _ = pathFirstMinimumMap j ≫ reflectedSimplexMap
    ((weightedKanHomCompositeDiagram F G x σ τ s).app j)
  rw [weightedKanHomCompositeDiagram_app]
  exact weightedConeCutCoefficient_one x (F.val.obj (σ.obj j)) (G.val.obj (σ.obj j))
    (stdSimplex.objEquiv t).toOrderHom ht j (τ.app j) _

/-- 時刻一の coslice 単体は、元の全変換による weighted 作用後の同じ比較単体。 -/
lemma weightedKanLeftCutCosliceSimplex_one {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (ht : ∀ j, (stdSimplex.objEquiv t).toOrderHom j = 1) :
    weightedKanLeftCutCosliceSimplex F G x σ τ s t =
      weightedCosliceSimplex G.val x ⟨σ, weightedKanHomCompositeDiagram F G x σ τ s⟩ := by
  apply Subtype.ext
  exact congrArg (fun A : SpaceInfinity.{u} _⦋n + 1⦌ =>
    (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm A)
      (weightedKanLeftCutConeSimplex_one F G x σ τ s t ht)

/-- 元の全 Hom に沿う weighted 係数の反転後合成を、同じ宇宙へ持ち上げた実際の族。 -/
def weightedKanHomCompositeFamily {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (weightedNerve (simplicialHomDiagram F.val x ⋙ SSet.opFunctor)) ⊗
        (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom F G).op ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj
      (weightedNerve (simplicialHomDiagram G.val x ⋙ SSet.opFunctor)) :=
  (uliftTensorIso _ _).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
    (((weightedNerve (simplicialHomDiagram F.val x ⋙ SSet.opFunctor)) ◁
      kanDiagramReflectedHomPostcomposition F G x) ≫
      weightedNerveMappingFamily (simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
        (simplicialHomDiagram G.val x ⋙ SSet.opFunctor))

/-- 全 weighted 係数・全 Hom の prism の終点は、元の weighted 作用後の coslice 比較。 -/
lemma weightedKanLeftCutCoslicePrism_one {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) :
    (prismEndpoint 1 _ ▷ _) ≫ weightedKanLeftCutCoslicePrism F G x =
      weightedKanHomCompositeFamily F G x ≫ weightedCosliceComparison G.val x := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨⟨σ, τ⟩⟩, s⟩
  exact weightedKanLeftCutCosliceSimplex_one F G x σ τ s.down _ (fun _ => rfl)

end SerrePositivity.InfinityCategories
