module

public import SerrePositivity.InfinityCategories.F2.StrictCoherentNatTrans
public import SerrePositivity.InfinityCategories.F2.CoherentEdges
public import SerrePositivity.InfinityCategories.Core.EquivalencePathIso

/-!
概要：自然変換の coherent 円柱の成分と図式全体の同型。
方針：垂直辺を指定成分と同定し、点ごとの可逆性を関手の同型へ送る。
規約：対象と Hom の宇宙は異なってよい。
使われ方：Cat_∞ 内の元の cospan と path 置換後の cospan の同値。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

omit [SimplicialCategory C] in
/-- 概要：通常の nerve の円柱の垂直辺は指定自然変換の成分。
方針：二点の対象と唯一の生成射の像を計算する。
規約：元の成分そのものを等式で回収する。
使われ方：coherent な垂直辺の可逆性の検証。 -/
lemma resizedNatTransMap_component {F G : I ⥤ C} (η : F ⟶ G) (i : I) :
    (resizedNatTransMap η).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})),
        PinchedHom.constant (ULift.up (ComposableArrows.mk₀ i)) 1) =
      ComposableArrows.mk₁ (η.app i) := by
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change η.app i ≫ G.map (𝟙 i) = η.app i
    simp
/-- 概要：coherent 円柱の垂直辺は指定成分の coherent な辺。
方針：通常の nerve の成分の等式に coherent 表示を適用する。
規約：元の関手の射の辺を選択せずに回収する。
使われ方：成分ごとの同値から図式全体の同型を作る。 -/
lemma strictCoherentNatTransMap_component {F G : I ⥤ C} (η : F ⟶ G) (i : I) :
    (strictCoherentNatTransMap η).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})),
        PinchedHom.constant (ULift.up (ComposableArrows.mk₀ i)) 1) =
      (coherentNerveEdge (η.app i)).edge := by
  change (nerveToCoherent C).app _ ((resizedNatTransMap η).app _ _) = _
  rw [resizedNatTransMap_component]
  rfl
/-- 概要：各成分が可逆な自然変換は strict coherent 図式の同型を与える。
方針：全頂点を通常の対象として表示し、円柱の垂直辺の可逆性を検証する。
規約：標的 coherent nerve の quasicategory 性を明示する。
使われ方：Cat_∞ の cospan の path 置換の前後の比較。 -/
def strictCoherentNatTransIso [Quasicategory (SimplicialNerve C)] {F G : I ⥤ C}
    (η : F ⟶ G) (hη : ∀ i, IsInvertibleEdge (coherentNerveEdge (η.app i))) :
    FunctorIso (HomotopyLimits.strictCoherentDiagram F)
      (HomotopyLimits.strictCoherentDiagram G) := by
  have e := functorIsoOfEquivalenceHomotopy (strictCoherentNatTransMap η) (by
    intro x
    have hx : x = ULift.up (ComposableArrows.mk₀ (x.down.obj 0)) := by
      apply ULift.ext
      exact ComposableArrows.ext₀ rfl
    rw [hx, strictCoherentNatTransMap_component]
    exact (isInvertibleEdge_congr (e := edgeOfSimplex _)
      (f := coherentNerveEdge (η.app (x.down.obj 0))) rfl).mpr (hη _))
  rw [strictCoherentNatTransMap_zero, strictCoherentNatTransMap_one] at e
  exact e

end SerrePositivity.InfinityCategories.F2
