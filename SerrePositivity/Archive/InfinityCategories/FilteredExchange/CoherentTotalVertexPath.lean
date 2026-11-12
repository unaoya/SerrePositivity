module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ContinuousKanSpecifiedHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-!
概要：指定した全空間円柱を元の余極限頂点の値の間の円柱へ移す。
方針：単位上の全円柱を厳密に保つ Kan 延長を使い、頂点表示だけを移す。
規約：Q の豊穣性を仮定しない。使われ方：元の cospan の指定可換 path の保持。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の全円柱に単位上で厳密に制限する Kan 置換後の円柱。
方針：指定円柱の anodyne 延長から全データを取る。
規約：元の円柱との等式も保持。使われ方：全 path の移送。 -/
def specifiedContinuousKanHomotopy {A X : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) :
    {L : SSet.Homotopy (continuousKanReplacement.map f) (continuousKanReplacement.map g) //
      (continuousKanReplacementUnit.app A ▷ (Δ[1] : SSet.{u})) ≫ L.h =
        H.h ≫ continuousKanReplacementUnit.app X} :=
  Classical.choice <| by
  obtain ⟨L, hL⟩ := continuousKanReplacement_specified_homotopy H
  exact ⟨⟨L, hL⟩⟩

variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
  {f g : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G}
  (H : SSet.Homotopy f g)

/-- 概要：元の指定円柱の Kan 延長を元の余極限頂点の値の間に表示。
方針：両頂点の表示の厳密な往復で前後合成。
規約：延長の全円柱を使用。使われ方：元の指定可換同型の値の表示。 -/
def coherentTotalVertexPathHomotopy :
    SSet.Homotopy (coherentTotalVertexMap F G f) (coherentTotalVertexMap F G g) := by
  let L := (specifiedContinuousKanHomotopy H).val
  simpa only [coherentTotalVertexMap, Category.assoc] using
    functorHomotopyPostcomp
      (functorHomotopyPrecomp L (eqToHom (coherentDiagramTotalVertex_object F)))
      (eqToHom (coherentDiagramTotalVertex_object G).symm)

/-- 概要：頂点表示の円柱は指定 Kan 延長の元の円柱の前後合成。
方針：構成の定義。規約：全円柱の等式。使われ方：単位への制限。 -/
lemma coherentTotalVertexPathHomotopy_h :
    (coherentTotalVertexPathHomotopy F G H).h =
      (eqToHom (coherentDiagramTotalVertex_object F) ▷ (Δ[1] : SSet.{u})) ≫
        (specifiedContinuousKanHomotopy H).val.h ≫
          eqToHom (coherentDiagramTotalVertex_object G).symm := rfl

/-- 概要：元の単位による制限は指定された元の全円柱の像そのもの。
方針：頂点表示の往復と指定 Kan 延長の単位上の厳密な式。
規約：全単体・全時刻で一致。使われ方：元の可換 path の保持。 -/
lemma coherentTotalVertexPathHomotopy_unit :
    (coherentDiagramTotalUnit F ▷ (Δ[1] : SSet.{u})) ≫
      (coherentTotalVertexPathHomotopy F G H).h = H.h ≫ coherentDiagramTotalUnit G := by
  rw [coherentTotalVertexPathHomotopy_h, ← comp_whiskerRight_assoc,
    coherentDiagramTotalUnit_factor, ← Category.assoc,
    (specifiedContinuousKanHomotopy H).property]
  rfl

/-- 概要：元の指定円柱が定める余極限頂点の値の間の可換同型。
方針：同じ指定円柱の辺の類。規約：新しい円柱を選ばない。使われ方：二射影の同時比較。 -/
def coherentTotalVertexPathIso :
    FunctorIso (coherentTotalVertexMap F G f) (coherentTotalVertexMap F G g) :=
  functorIsoOfSimplicialHomotopy (coherentTotalVertexPathHomotopy F G H)

end SerrePositivity.InfinityCategories.F2
