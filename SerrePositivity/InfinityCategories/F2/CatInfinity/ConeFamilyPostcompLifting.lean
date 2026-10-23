module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeFamilyPostcomp
public import SerrePositivity.InfinityCategories.F1B.KanCoconeFamilyEquivalenceLifting

/-!
概要：図式固定の錐の族の後合成の充填性。
方針：相対内部 Hom の充填性を元の図式の頂点 fiber に制限する。
規約：図式は高次の全パラメータを通じて固定する。
使われ方：引き戻しの錐族の写像空間の Kan fibration 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：inner fibration による錐族の後合成は inner fibration。
方針：錐の形の相対内部 Hom の比較から fiber の充填性を得る。
規約：図式の添字に quasicategory 性を要求しない。
使われ方：成分ごとの極限錐の厳密な比較。 -/
instance coneFamilyPostcomp_innerFibration {J X Y : SSet.{u}}
    (r : J ⟶ X) (f : X ⟶ Y) [InnerFibration f] :
    InnerFibration (coneFamilyPostcomp r f) := by
  let sq := Functor.PullbackObjObj.ofHasPullback internalHom
    (joinInr (Δ[0] : SSet.{u}) J) f
  have hi : InnerFibration sq.π := innerFibration_pullbackObjObjπ sq
  exact @F1B.kanRelativeVertexFiberMap_innerFibration _ _ _ _
    (coneRestriction J X) (coneRestriction J Y)
    ((ihom (join (Δ[0] : SSet.{u}) J)).map f) ((ihom J).map f)
    ((pre (joinInr (Δ[0] : SSet.{u}) J)).naturality f).symm hi (functorVertex r)

/-- 概要：同値を持ち上げる射による錐族の後合成も同値を持ち上げる。
方針：相対内部 Hom の右持ち上げ条件を図式の頂点 fiber へ制限する。
規約：添字と図式に単射性を要求しない。
使われ方：錐族の写像空間での Kan fibration による普遍性。 -/
lemma coneFamilyPostcomp_equivalenceLifting {J X Y : SSet.{u}}
    (r : J ⟶ X) (f : X ⟶ Y) (hf : F1B.KanEquivalenceLifting f) :
    F1B.KanEquivalenceLifting (coneFamilyPostcomp r f) := by
  let sq := Functor.PullbackObjObj.ofHasPullback internalHom
    (joinInr (Δ[0] : SSet.{u}) J) f
  have hs : F1B.KanEquivalenceLifting sq.π :=
    F1B.KanEquivalenceLifting.relativeInternalHom hf
    (joinInr (Δ[0] : SSet.{u}) J) sq
  intro A T i hm hi
  exact F1B.kanRelativeVertexFiberMap_equivalenceLifting
    (coneRestriction J X) (coneRestriction J Y)
    ((ihom (join (Δ[0] : SSet.{u}) J)).map f) ((ihom J).map f)
    ((pre (joinInr (Δ[0] : SSet.{u}) J)).naturality f).symm hs (functorVertex r) i hm hi

end SerrePositivity.InfinityCategories.F2
