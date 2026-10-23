module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalVertexPath
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.HomotopyIsoWhiskering

/-!
概要：余極限頂点の表示への移送は指定 Kan 延長の同型の等式を保つ。
方針：同じ円柱の前後合成を指定同型の whisker として表示する。
規約：元の指定値を保持。使われ方：底固定模型の path と既存の値の可換同型の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
  {f g : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G}

/-- 概要：頂点の値の表示への path 同型は元の指定 Kan 同型の前後合成。
方針：同じ円柱の前後合成の類を計算。
規約：指定同型の等式。使われ方：元の頂点表示を介する比較。 -/
lemma coherentTotalVertexPathIso_eq_whisker (H : SSet.Homotopy f g) :
    coherentTotalVertexPathIso F G H =
      ((functorIsoOfSimplicialHomotopy (specifiedContinuousKanHomotopy H).val).precomp
        (eqToHom (coherentDiagramTotalVertex_object F))).postcomp
          (eqToHom (coherentDiagramTotalVertex_object G).symm) := by
  change functorIsoOfSimplicialHomotopy (functorHomotopyPostcomp
    (functorHomotopyPrecomp (specifiedContinuousKanHomotopy H).val
      (eqToHom (coherentDiagramTotalVertex_object F)))
    (eqToHom (coherentDiagramTotalVertex_object G).symm)) = _
  rw [homotopyIso_postcomp, homotopyIso_precomp]

/-- 概要：指定 Kan 同型の等式は元の余極限頂点の値の指定同型の等式へ移る。
方針：同じ前後合成で等式を写す。
規約：元の値の射を保持。使われ方：二つの円柱代表からの同型の照合。 -/
lemma coherentTotalVertexPathIso_eq_of_kan_iso (H K : SSet.Homotopy f g)
    (h : functorIsoOfSimplicialHomotopy (specifiedContinuousKanHomotopy H).val =
      functorIsoOfSimplicialHomotopy (specifiedContinuousKanHomotopy K).val) :
    coherentTotalVertexPathIso F G H = coherentTotalVertexPathIso F G K := by
  rw [coherentTotalVertexPathIso_eq_whisker, coherentTotalVertexPathIso_eq_whisker, h]

end SerrePositivity.InfinityCategories.F2
