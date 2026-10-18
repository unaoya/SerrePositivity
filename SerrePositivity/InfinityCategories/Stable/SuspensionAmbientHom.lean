module
public import SerrePositivity.InfinityCategories.Stable.CofiberConnectingNaturality

/-! # 懸垂図式間の任意の射と懸垂関手

概要：四角形の関手圏の h の射でも、懸垂間の射は始点成分から懸垂関手で計算できる。
方針：始点の射の標準持ち上げと普遍性による一意性で比較する。
規約：射が全部分圏から来るという追加条件は不要。使われ方：回転の第三接続射の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：懸垂図式間の射は、指定した始点成分を懸垂関手で送った射を終点に持つ。
方針：始点成分の一致から標準持ち上げとの一致を示し、その終点の自然性を使う。
規約：端点の指定等号による輸送を明記。使われ方：幾何学的な回転比較の関手的解釈。 -/
lemma SuspensionSquare.ambientHom_target {X : SSet.{u}} [Quasicategory X] [IsStable X]
    {x y : X _⦋0⦌} (s : SuspensionSquare x) (r : SuspensionSquare y)
    (a : (SSet.HomotopyCategory.mk (functorVertex s.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (functorVertex r.square))
    (f : SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y)
    (hsource : (squareDiagramHoEvaluation X 0 0).map a =
      eqToHom (congrArg SSet.HomotopyCategory.mk s.source_eq) ≫ f ≫
        eqToHom (congrArg SSet.HomotopyCategory.mk r.source_eq.symm)) :
    (squareDiagramHoEvaluation X 1 1).map a ≫ r.suspensionFunctorObjIso.inv =
      s.suspensionFunctorObjIso.inv ≫ (suspensionFunctor X).map f := by
  have ha : a = (suspensionDiagramHoInclusion X).map (s.liftSourceHom r f) := by
    apply cofiberSuspensionComparison_hom_ext s.square s.isPushout r
    change (squareDiagramHoEvaluation X 0 0).map _ =
      (squareDiagramHoEvaluation X 0 0).map _
    rw [hsource, suspensionDiagramHoInclusion_evaluation, SuspensionSquare.liftSourceHom_source]
  rw [ha, suspensionDiagramHoInclusion_evaluation]
  exact s.suspensionFunctorObjIso_inv_naturality r f

end SerrePositivity.InfinityCategories
