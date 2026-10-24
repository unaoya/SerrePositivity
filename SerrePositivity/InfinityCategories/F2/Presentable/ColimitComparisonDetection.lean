module

public import SerrePositivity.InfinityCategories.F2.Ind.HomotopyColimitValueDetection
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluationNaturality
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
概要：余極限を保つ二関手の指定比較の可逆性を生成図式から検出する。
方針：同じ比較のホモトピー代表へ余極限頂点の可逆性判定を適用する。
規約：比較射自身を固定し、頂点同型にも自然性で移す。
使われ方：filtered と幾何学的実現で生成された P_Σ の保存判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：同型な二頂点で指定比較成分の可逆性は同値。
方針：同じ h 圏自然変換の同型に関する自然性を使う。
規約：比較成分を選び直さない。
使われ方：生成表示の頂点同型に沿う検出。 -/
lemma functorHomEvaluate_isIso_iff_vertexIso
    {X Y : SSet.{u}} [Quasicategory Y] {F G : X ⟶ Y}
    (η : FunctorHom F G) {x y : X _⦋0⦌} (e : VertexIso x y) :
    IsIso (functorHomEvaluate η x) ↔ IsIso (functorHomEvaluate η y) := by
  simpa only [functorCellToNatTrans_app_eq_evaluate] using
    NatTrans.isIso_app_iff_of_iso (functorCellToNatTrans η) e

/-- 概要：指定比較が図式上で可逆なら保存された余極限頂点でも可逆。
方針：同じ射のホモトピー代表に既存の余極限可逆性検出を適用する。
規約：元の全余錐と指定比較を保持する。
使われ方：二段階の生成に沿う同型検出。 -/
lemma functorHomEvaluate_isIso_of_colimit
    {K X Y : SSet.{u}} [Quasicategory Y] {p : K ⟶ X}
    (c : JoinCocone p) {F G : X ⟶ Y}
    (hF : IsColimitCone (mapJoinCocone F c))
    (hG : IsColimitCone (mapJoinCocone G c)) (η : FunctorHom F G)
    (hη : ∀ j, IsIso (functorHomEvaluate η (p.app (Opposite.op ⦋0⦌) j))) :
    IsIso (functorHomEvaluate η c.vertex) := by
  have h := Ind.homotopy_colimit_value_isInvertible c hF hG
    (functorHomHomotopy η) (fun j ↦ ?_)
  · change IsIso (SSet.Truncated.HomotopyCategory.homMk _) at h
    rwa [functorHomHomotopy_component] at h
  · change IsIso (SSet.Truncated.HomotopyCategory.homMk _)
    rw [functorHomHomotopy_component]
    exact hη j

end SerrePositivity.InfinityCategories.F2.Presentable
