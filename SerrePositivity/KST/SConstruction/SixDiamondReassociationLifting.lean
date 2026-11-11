module
public import SerrePositivity.KST.SConstruction.SixDiamondReassociations
public import SerrePositivity.KST.SConstruction.CompositionTripleInputTransport

/-! # 六つの結合替えを全基底像と全共有面を保って同時に持ち上げる
概要：fibration に沿い、元の全六四面体と最後の全残面を同じ共有面で持ち上げる。
方針：各出力面の厳密な射影式で次の基底入力表示を合わせ、六回の実持ち上げを合成する。
規約：各四面体の全基底像を保持し、六つの独立な選択や類の等号にしない。
使われ方：元の高次 prism に沿う実六対角面消去の相対構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
variable {E : SSet.{u}} {v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : E _⦋0⦌}
  {s t : E.Edge v₀ v₁} {leftEdge generatedEdge : E.Edge v₁ v₂}
  {r : E.Edge v₂ v₃} {p₀ : E.Edge v₀ v₄} {l : E.Edge v₄ v₂}
  {q : E.Edge v₄ v₅} {k₁ : E.Edge v₀ v₆} {k₂ : E.Edge v₆ v₅}
  {k₃ : E.Edge v₅ v₃} {a : E.Edge v₆ v₇} {e : E.Edge v₇ v₃} {b : E.Edge v₁ v₇}
  {topEdge : E.Edge v₀ v₃} {bottomEdge : E.Edge v₀ v₂}

/-- 元の全面・全共有面・同じ全基底六四面体を保持する実持ち上げ。 -/
structure SixDiamondReassociationsOver
    (DA : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond p₀ q k₁ k₂) (DB : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a e k₂ k₃)
    (DI : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond l r q k₃) (DL : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond s leftEdge p₀ l)
    (DR : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond t b k₁ a) (DF : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond b e generatedEdge r)
    (top : SSet.Edge.CompStruct DL.diagonal r topEdge)
    (bottom : SSet.Edge.CompStruct t generatedEdge bottomEdge)
    {B : SSet.{u}} (p : E ⟶ B)
    (R : SixDiamondReassociations (DA.map p) (DB.map p) (DI.map p)
      (DL.map p) (DR.map p) (DF.map p) (top.map p) (bottom.map p)) where
  /-- 元の十二面と全共有面を持つ同じ六結合替え。 -/
  pasting : SixDiamondReassociations DA DB DI DL DR DF top bottom
  /-- 第1全四面体の射影を厳密に保持する。 -/
  first_projection :
    SSet.yonedaEquiv.symm pasting.firstMove.simplex ≫ p =
      SSet.yonedaEquiv.symm R.firstMove.simplex
  /-- 第2全四面体の射影を厳密に保持する。 -/
  second_projection :
    SSet.yonedaEquiv.symm pasting.secondMove.simplex ≫ p =
      SSet.yonedaEquiv.symm R.secondMove.simplex
  /-- 第3全四面体の射影を厳密に保持する。 -/
  third_projection :
    SSet.yonedaEquiv.symm pasting.thirdMove.simplex ≫ p =
      SSet.yonedaEquiv.symm R.thirdMove.simplex
  /-- 第4全四面体の射影を厳密に保持する。 -/
  fourth_projection :
    SSet.yonedaEquiv.symm pasting.fourthMove.simplex ≫ p =
      SSet.yonedaEquiv.symm R.fourthMove.simplex
  /-- 第5全四面体の射影を厳密に保持する。 -/
  fifth_projection :
    SSet.yonedaEquiv.symm pasting.fifthMove.simplex ≫ p =
      SSet.yonedaEquiv.symm R.fifthMove.simplex
  /-- 第6全四面体の射影を厳密に保持する。 -/
  sixth_projection :
    SSet.yonedaEquiv.symm pasting.sixthMove.simplex ≫ p =
      SSet.yonedaEquiv.symm R.sixthMove.simplex
  /-- 最後の全残面の射影を、次の終辺消去の同じ全面として保持する。 -/
  residual_eq : pasting.sixthMove.left.map p = R.sixthMove.left

variable
    (DA : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond p₀ q k₁ k₂) (DB : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a e k₂ k₃)
    (DI : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond l r q k₃) (DL : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond s leftEdge p₀ l)
    (DR : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond t b k₁ a) (DF : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond b e generatedEdge r)
    (top : SSet.Edge.CompStruct DL.diagonal r topEdge)
    (bottom : SSet.Edge.CompStruct t generatedEdge bottomEdge)
    {B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (R : SixDiamondReassociations (DA.map p) (DB.map p) (DI.map p)
      (DL.map p) (DR.map p) (DF.map p) (top.map p) (bottom.map p))

/-- 六つの全結合替えを、同じ全基底像と全共有面を保って逐次持ち上げる。 -/
def sixDiamondReassociationsLiftData : SixDiamondReassociationsOver
    DA DB DI DL DR DF top bottom p R := by
  let M₁ := compositionTripleRightTetrahedronLiftData DL.second DI.first top p R.firstMove
  have h₁ : M₁.val.right.map p = R.firstMove.right :=
    compositionTripleRightTetrahedronLiftData_right_eq DL.second DI.first top p R.firstMove
  let B₂ := compositionTripleInputTransport (DA.first.map p) (DI.second.map p) h₁.symm
    R.secondMove
  let M₂ := compositionTripleTetrahedronLiftData DA.first DI.second M₁.val.right p B₂.val
  have h₂ : M₂.val.left.map p = R.secondMove.left :=
    (compositionTripleTetrahedronLiftData_left_eq DA.first DI.second M₁.val.right p B₂.val).trans
      B₂.property.2
  let B₃ := compositionTripleRightInputTransport (DA.second.map p) (DB.second.map p) h₂.symm
    R.thirdMove
  let M₃ := compositionTripleRightTetrahedronLiftData DA.second DB.second M₂.val.left p B₃.val
  have h₃ : M₃.val.right.map p = R.thirdMove.right :=
    (compositionTripleRightTetrahedronLiftData_right_eq
      DA.second DB.second M₂.val.left p B₃.val).trans
      B₃.property.2
  let B₄ := compositionTripleInputTransport (DR.second.map p) (DB.first.map p) h₃.symm
    R.fourthMove
  let M₄ := compositionTripleTetrahedronLiftData DR.second DB.first M₃.val.right p B₄.val
  have h₄ : M₄.val.left.map p = R.fourthMove.left :=
    (compositionTripleTetrahedronLiftData_left_eq DR.second DB.first M₃.val.right p B₄.val).trans
      B₄.property.2
  let B₅ := compositionTripleRightInputTransport (DR.first.map p) (DF.first.map p) h₄.symm
    R.fifthMove
  let M₅ := compositionTripleRightTetrahedronLiftData DR.first DF.first M₄.val.left p B₅.val
  have h₅ : M₅.val.right.map p = R.fifthMove.right :=
    (compositionTripleRightTetrahedronLiftData_right_eq
      DR.first DF.first M₄.val.left p B₅.val).trans
      B₅.property.2
  let B₆ := compositionTripleInputTransport (bottom.map p) (DF.second.map p) h₅.symm
    R.sixthMove
  let M₆ := compositionTripleTetrahedronLiftData bottom DF.second M₅.val.right p B₆.val
  have h₆ : M₆.val.left.map p = R.sixthMove.left :=
    (compositionTripleTetrahedronLiftData_left_eq bottom DF.second M₅.val.right p B₆.val).trans
      B₆.property.2
  refine ⟨⟨M₁.val, M₂.val, M₃.val, M₄.val, M₅.val, M₆.val⟩, M₁.property.1,
    ?_, ?_, ?_, ?_, ?_, h₆⟩
  · exact M₂.property.1.trans (congrArg SSet.yonedaEquiv.symm B₂.property.1)
  · exact M₃.property.1.trans (congrArg SSet.yonedaEquiv.symm B₃.property.1)
  · exact M₄.property.1.trans (congrArg SSet.yonedaEquiv.symm B₄.property.1)
  · exact M₅.property.1.trans (congrArg SSet.yonedaEquiv.symm B₅.property.1)
  · exact M₆.property.1.trans (congrArg SSet.yonedaEquiv.symm B₆.property.1)

end SerrePositivity.KST.SConstruction
