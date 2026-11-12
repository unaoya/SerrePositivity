module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.DoubleSubdivisionHornMap
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornSubdivisionInclusion
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornChainBoundary

/-!
# 二重細分から horn への写像の境界条件

概要：具体的に構成した写像は、二重細分された horn 上で反復最終頂点写像に一致する。
方針：horn の細分比較の包含との可換性、nerve の比較の自然性、有限鎖上の境界条件を合成する。
規約：Moss 2020 Proposition 21 の有限段階の充填に使う境界の等式。
使われ方：Ex の二回の適用後の horn の写像の充填。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory PartialOrder
open scoped _root_.Simplicial

/--
概要：二重細分から horn への具体的な写像の horn 上の制限は反復最終頂点である。
方針：面の nerve を経由する比較を順に自然性で移し、最終頂点の自然性でまとめる。
規約：Moss 2020 Proposition 21 の Kan 性へ向けた有限段階の境界条件。
使われ方：随伴を二度適用して Ex の horn の充填を得る。
-/
@[reassoc] theorem doubleSubdivisionHornMap_boundary (n : ℕ) (hn : 0 < n)
    (k : Fin (n + 1)) :
    SSet.sd.map (SSet.sd.map (SSet.horn.{u} n k).ι) ≫ doubleSubdivisionHornMap n hn k =
      subdivisionLastVertexMap.app (SSet.sd.obj (SSet.horn n k)) ≫
        subdivisionLastVertexMap.app (SSet.horn n k) := by
  let H := (SSet.horn.{u} n k : SSet.{u})
  let P := HornFacePoset.{u} n k
  let F := NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))
  change SSet.sd.map (SSet.sd.map (SSet.horn n k).ι) ≫
    (SSet.sd.map (SSet.stdSimplex.sdIso.hom.app ⦋n⦌) ≫
      subdivisionNerveChains F ≫ hornChainToHorn n hn k) = _
  calc
    _ = SSet.sd.map (SSet.sd.map (SSet.horn n k).ι ≫
        SSet.stdSimplex.sdIso.hom.app ⦋n⦌) ≫
        subdivisionNerveChains F ≫ hornChainToHorn n hn k := by
      simp only [SSet.sd.map_comp, Category.assoc]
    _ = SSet.sd.map (hornSubdivisionComparison n k ≫
        nerveMap (hornFaceInclusion n k).monotone.functor) ≫
        subdivisionNerveChains F ≫ hornChainToHorn n hn k := by
      rw [hornSubdivisionComparison_inclusion]
    _ = SSet.sd.map (hornSubdivisionComparison n k) ≫
        subdivisionNerveChains P ≫
        nerveMap (NonemptyFiniteChains.orderHomMap (hornFaceInclusion n k)).monotone.functor ≫
        hornChainToHorn n hn k := by
      rw [SSet.sd.map_comp, Category.assoc, subdivisionNerveChains_naturality_assoc]
    _ = SSet.sd.map (hornSubdivisionComparison n k) ≫
        subdivisionNerveChains P ≫
        nerveMap (finiteChainGreatest (P := P)).monotone.functor ≫
        hornFacesLastVertex n k := by rw [hornChainToHorn_boundary]
    _ = SSet.sd.map (hornSubdivisionComparison n k) ≫
        subdivisionLastVertexMap.app (nerve P) ≫ hornFacesLastVertex n k := by
      rw [subdivisionNerveChains_lastVertex_assoc]
    _ = subdivisionLastVertexMap.app (SSet.sd.obj H) ≫
        hornSubdivisionComparison n k ≫ hornFacesLastVertex n k := by
      rw [subdivisionLastVertexMap.naturality_assoc]
      rfl
    _ = _ := by rw [hornSubdivisionComparison_lastVertex]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
