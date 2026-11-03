module
public import SerrePositivity.InfinityCategories.Derived.CofiberSuspensionComparisonData
public import SerrePositivity.InfinityCategories.Derived.ComplexSquareMiddleHomotopy
public import SerrePositivity.InfinityCategories.Core.HomotopyEvaluationClass
public import SerrePositivity.InfinityCategories.Stable.HomotopyEndpointTransport

/-! # 標準 cofiber から標準 suspension への四角形比較

概要：cone 写像への後合成と中間対象の零への変更を、四角形関手圏の h の射として合成する。
方針：変更後の全データの同定でホモトピーの終端を標準 suspension に合わせる。
規約：実際のホモトピーを保持する。使われ方：D7 の接続射の選択との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S] {A B : Complex S}

/-- 終点への後合成後に中間対象を零に送る、実際の四角形ホモトピー。 -/
def cofiberToSuspensionMiddleHomotopy (f : A ⟶ B) : SSet.Homotopy (Y := dgNerve S (Complex S))
    ((cofiberComplexSquareData f (0 : A ⟶ 0)).postcompose (cofiberToSuspensionMap f)).square
    (cofiberComplexSquareData (0 : A ⟶ 0) (0 : A ⟶ 0)).square :=
  homotopyOfEndpoints
    (((cofiberComplexSquareData f (0 : A ⟶ 0)).postcompose
      (cofiberToSuspensionMap f)).changeBottomMiddleHomotopy (0 : B ⟶ 0)
        (pushoutInclusionB (0 : A ⟶ 0) (0 : A ⟶ 0)) (cofiberToSuspensionRightFactor f)) rfl
    (congrArg (fun k : ComplexSquareData A 0 0
      (pushoutCofiber (0 : A ⟶ 0) (0 : A ⟶ 0)) => k.square)
        (cofiberToSuspensionIntermediateData_eq f))

/-- 全複体の dg nerve における cofiber から suspension への四角形比較射。 -/
def cofiberToSuspensionSquareHom (f : A ⟶ B) :
    (SSet.HomotopyCategory.mk (functorVertex (cofiberComplexSquareData f (0 : A ⟶ 0)).square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (dgNerve S (Complex S)))) ⟶
      SSet.HomotopyCategory.mk (functorVertex
        (cofiberComplexSquareData (0 : A ⟶ 0) (0 : A ⟶ 0)).square) :=
  SSet.Truncated.HomotopyCategory.homMk
      ((cofiberComplexSquareData f (0 : A ⟶ 0)).postcomposeSquareEdge (cofiberToSuspensionMap f)) ≫
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (cofiberToSuspensionMiddleHomotopy f))

end SerrePositivity.InfinityCategories
