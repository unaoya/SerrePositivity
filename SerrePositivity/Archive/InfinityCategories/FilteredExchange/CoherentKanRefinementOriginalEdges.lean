module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentKanRefinementIntervalEdges
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite

/-!
概要：元の精密化とその反転を、同じ左右区間族の両端付き実辺として保持する。
方針：元の一単体の辺を反転・宇宙持ち上げで写し、元の区間族へ送る。
規約：逆辺を選ばず、元の一単体と実両端を保持する。
使われ方：共通解像の消去式を元の指定精密化の二つの実辺へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (K L : KanObject.{u}) (e : (SimplicialCategory.sHom K L) _⦋1⦌)
local notation "H" => SimplicialCategory.sHom K L
local notation "Y" => intervalMappingSpace (spaceInfinityVertex K) (spaceInfinityVertex L)

/-- 元の精密化を元の右区間族へ送った同じ実辺。 -/
def coherentKanRightRefinementEdge : SSet.Edge (X := Y)
    ((coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌) (ULift.up ((H).δ 1 e)))
    ((coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌) (ULift.up ((H).δ 0 e))) :=
  (SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} (edgeOfSimplex e))).map
    (coherentKanRightHomInterval K L)

/-- 元の反転精密化を元の左区間族へ送った同じ実辺。 -/
def coherentKanLeftRefinementEdge : SSet.Edge (X := Y)
    ((coherentKanLeftHomInterval K L).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm ((H).δ 0 e))))
    ((coherentKanLeftHomInterval K L).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm ((H).δ 1 e)))) :=
  (SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} (edgeOp (edgeOfSimplex e)))).map
    (coherentKanLeftHomInterval K L)

end SerrePositivity.InfinityCategories.F2
