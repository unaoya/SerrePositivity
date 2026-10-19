module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeInternalHomLifting
public import SerrePositivity.InfinityCategories.F1B.KanRelativeCoconeFamilyInitial

/-!
概要：isofibration の上で図式固定の余錐の族の同型を持ち上げるための充填性。
方針：相対内部 Hom の右持ち上げを頂点 fiber の比較へ移す。
規約：元の図式は全時間を通じて固定する。
使われ方：標準底余錐と普遍 comma 底余錐の比較同型の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：引き戻しへの比較の同値持ち上げは頂点 fiber の比較へ移る。
方針：各試験射に既存の fiber 持ち上げの判定を適用する。
規約：二つの底の射 u は任意。
使われ方：固定図式の余錐の後合成の同値持ち上げ。 -/
lemma kanRelativeVertexFiberMap_equivalenceLifting {V W B C : SSet.{u}}
    (p : V ⟶ B) (q : W ⟶ C) (f : V ⟶ W) (u : B ⟶ C)
    (h : p ≫ u = f ≫ q) (hl : KanEquivalenceLifting (pullback.lift p f h))
    (b : B _⦋0⦌) : KanEquivalenceLifting (kanRelativeVertexFiberMap p q f u h b) := by
  intro A T i hm hi
  have := hl i hm hi
  exact kanRelativeVertexFiberMap_hasLiftingProperty p q f u h i b

/-- 概要：isofibration の上の図式固定の余錐の族の後合成も同値を持ち上げる。
方針：余錐制限の相対内部 Hom の持ち上げを図式の頂点 fiber へ制限する。
規約：添字 K と図式 p に quasicategory 性や単射性を要求しない。
使われ方：像の余錐の同型を元の図式を固定したまま持ち上げる。 -/
lemma kanCoconeFamilyPostcomp_equivalenceLifting {K D E : SSet.{u}}
    (p : K ⟶ D) (U : D ⟶ E) (hU : KanEquivalenceLifting U) :
    KanEquivalenceLifting (kanCoconeFamilyPostcomp p U) := by
  let sq := Functor.PullbackObjObj.ofHasPullback internalHom (joinInl K (Δ[0] : SSet.{u})) U
  have hs : KanEquivalenceLifting sq.π := hU.relativeInternalHom (joinInl K (Δ[0] : SSet.{u})) sq
  intro A T i hm hi
  have hl : HasLiftingProperty i (pullback.lift (coconeRestriction K D)
      ((ihom (join K (Δ[0] : SSet.{u}))).map U)
      ((pre (joinInl K (Δ[0] : SSet.{u}))).naturality U).symm) := by
    exact hs i hm hi
  exact @kanRelativeVertexFiberMap_hasLiftingProperty _ _ _ _ A T
    (coconeRestriction K D) (coconeRestriction K E)
    ((ihom (join K (Δ[0] : SSet.{u}))).map U) ((ihom K).map U)
    ((pre (joinInl K (Δ[0] : SSet.{u}))).naturality U).symm i hl (functorVertex p)

end SerrePositivity.InfinityCategories.F1B
