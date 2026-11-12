module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornSubdivisionComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionLastVertexMap

/-!
# horn の細分比較と最終頂点の一致

概要：horn の細分を面の nerve へ比較して最終頂点を取ると、実際の最終頂点写像に一致する。
方針：随伴形で各頂点を計算し、有限鎖の最大元と単調写像の交換を使う。
規約：Moss 2020 Proposition 21 の境界条件の一段階。
使われ方：二重細分の候補を Ex の単位の反復と比較する。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite PartialOrder
open scoped _root_.Simplicial

/--
概要：horn の面への Ex の比較の後で最終頂点を取ると、horn の Ex の単位となる。
方針：horn の包含で標準単体へ移し、各頂点で有限鎖の像の最大元を計算する。
規約：Moss 2020 Proposition 21 の境界条件の随伴形。
使われ方：horn の細分からの写像の一致を示す。
-/
theorem hornFacesExUnit_lastVertex (n : ℕ) (k : Fin (n + 1)) :
    hornFacesExUnit.{u} n k ≫ SSet.ex.map (hornFacesLastVertex n k) =
      exUnitAt (SSet.horn n k) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (cancel_mono (SSet.horn n k).ι).mp
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro t
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  let C : NonemptyFiniteChains (ULift.{u} (Fin (d.unop.len + 1))) := t.obj i
  change (finiteChainMaximum (C.map (hornSimplexOrderHom n k d.unop s))).down =
    SSet.stdSimplex.asOrderHom s.val (finiteChainMaximum C).down
  exact congrArg ULift.down (finiteChainMaximum_map (hornSimplexOrderHom n k d.unop s) C)

/--
概要：horn の細分比較から最終頂点への合成は、horn の実際の最終頂点写像に一致する。
方針：Ex の単位との一致を随伴同値で転置する。
規約：二重細分の horn 上の境界の計算。
使われ方：有限鎖の nerve での境界条件を horn の細分へ戻す。
-/
@[reassoc] theorem hornSubdivisionComparison_lastVertex (n : ℕ) (k : Fin (n + 1)) :
    hornSubdivisionComparison.{u} n k ≫ hornFacesLastVertex n k =
      subdivisionLastVertexMap.app (SSet.horn n k) := by
  apply (SSet.sdExAdjunction.homEquiv _ _).injective
  rw [SSet.sdExAdjunction.homEquiv_naturality_right]
  simpa only [hornSubdivisionComparison, subdivisionLastVertexMap,
    Functor.id_obj, Equiv.apply_symm_apply] using hornFacesExUnit_lastVertex n k

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
