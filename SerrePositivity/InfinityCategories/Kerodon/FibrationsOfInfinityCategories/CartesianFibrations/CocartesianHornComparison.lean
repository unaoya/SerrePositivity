module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration

/-!
概要：F1 の cocartesian fibration と Core の端点を指定したホーン充填の界面を比較する。
方針：一単体と型付き辺の表現、および HasLift と実際の充填の存在を往復する。
規約：構造の比較は明示的な定理とし、相互に循環する instance を追加しない。
使われ方：相対指数の構成で F1 の輸送と Core の相対ホモトピー延長を併用する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：一単体としての cocartesian 性は型付き辺の外側ホーン充填と同値。
方針：可換正方形の持ち上げと実際の射の存在を往復する。
規約：射の inner fibration 性は不要。
使われ方：Core と F1 の輸送の界面の接続。 -/
lemma isCocartesianEdge_iff_hasCocartesianHornLifting {E B : SSet.{u}} (p : E ⟶ B)
    {x y : E _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj E) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e.edge ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p e := by
  constructor
  · intro he n a b hab hw
    have sq : CommSq a (horn (n + 2) 0).ι p b := ⟨hw⟩
    have := he n a b hab sq
    exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩
  · intro he n a b hab sq
    obtain ⟨F, hF, hFp⟩ := he n a b hab sq.w
    exact CommSq.HasLift.mk' { l := F, fac_left := hF, fac_right := hFp }

/-- 概要：F1 の cocartesian fibration は Core の始点指定の輸送を持つ。
方針：型付き基底辺を標準区間の射に直し、持ち上げた一単体に端点の型を付ける。
規約：quasicategory 性は不要で、定理を明示的に適用して使う。
使われ方：Core の cocartesian なホモトピー延長を F1 の入力へ適用する。 -/
lemma CocartesianFibration.toCocartesianHornFibration {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p where
  mem := InnerFibration.mem
  exists_lift x b a := by
    have ha : stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm a.edge =
        SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) := by
      apply SSet.yonedaEquiv.injective
      rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact a.src_eq
    obtain ⟨F, hF, hFp, hFc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration.mem (p := p) |>.2 x _ ha
    have hs : E.δ 1 (SSet.yonedaEquiv F) = x := by
      rw [← stdSimplex.yonedaEquiv_δ_comp, hF, Equiv.apply_symm_apply]
    let e : SSet.Truncated.Edge (X := (truncation 2).obj E) x
        (E.δ 0 (SSet.yonedaEquiv F)) :=
      { edge := SSet.yonedaEquiv F, src_eq := hs, tgt_eq := rfl }
    refine ⟨_, e, ?_, (isCocartesianEdge_iff_hasCocartesianHornLifting p e).1 hFc⟩
    change p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = a.edge
    rw [← SSet.yonedaEquiv_comp, hFp, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
