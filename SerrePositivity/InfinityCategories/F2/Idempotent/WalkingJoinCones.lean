module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WalkingCones
public import SerrePositivity.InfinityCategories.F1B.KanNerveCoconeNaturality

/-!
概要：元の冪等包含の錐と余錐を、元の全 nerve 上の join の錐と余錐へ移す。
方針：F1B の通常の錐と native な錐の比較を、指定した元の歩行図式に適用する。
規約：頂点は元の分裂対象、指定した脚は元の包含と元の射影そのもの。
使われ方：強い分裂の元の全 Idem 図式への錐と余錐の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全冪等包含の native な余錐。 -/
def walkingJoinCocone : JoinCocone idemInclusion.{u} :=
  F1B.kanNerveCoconeEquiv walkingCocone

/-- 元の全冪等包含の native な錐。 -/
def walkingJoinCone : JoinCone idemInclusion.{u} := F1B.kanNerveCone walkingCone

/-- 元の余錐の点側への制限は、元の分裂頂点の包含。 -/
lemma walkingJoinCocone_point :
    joinInr IdemShape (Δ[0] : SSet.{u}) ≫ walkingJoinCocone.val = nervePoint walkingImage :=
  F1B.kanNerveCocone_point walkingCocone

/-- 元の錐の頂点は、元の分裂対象の同じ nerve 頂点。 -/
lemma walkingJoinCone_vertex : walkingJoinCone.{u}.vertex = nerveVertex walkingImage :=
  F1B.kanNerveCone_vertex walkingCone

/-- 元の余錐の指定した混合辺は、元の射影の同じ nerve 辺。 -/
lemma walkingJoinCocone_leg : walkingJoinCocone.{u}.val.app (Opposite.op ⦋1⦌)
    (F1B.kanJoinCoconeLegSimplex (nerveVertex walkingObject)) =
      ComposableArrows.mk₁ walkingRetraction :=
  F1B.kanNerveCocone_leg walkingCocone walkingObject

/-- 元の錐の指定した混合辺は、元の包含の同じ nerve 辺。 -/
lemma walkingJoinCone_leg : walkingJoinCone.{u}.val.app (Opposite.op ⦋1⦌)
    (F1B.kanConeLegSimplex walkingObject) = ComposableArrows.mk₁ walkingSection :=
  F1B.kanNerveCone_leg walkingCone walkingObject

end SerrePositivity.InfinityCategories.F2.Idempotent
