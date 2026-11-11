module
public import SerrePositivity.KST.SConstruction.FamilyCompStructRealization
public import SerrePositivity.KST.SConstruction.FamilyTriangleFaces

/-! # 元の全合成三角形の後合成と三円柱の表示変更
概要：元の全三角形を後合成し、同じ全三面を指定円柱の表示へ移す。
方針：元の全実二単体の写像を後合成して curry し、各面を厳密に照合する。
規約：全二単体を保持し、三面の存在や合成式を新たな仮定にしない。
使われ方：各段の span 比較の構造射像と次段の射影。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {U E B : SSet.{u}} {a b c : U ⟶ E}
  {first : SSet.Homotopy a b} {second : SSet.Homotopy b c} {direct : SSet.Homotopy a c}
  (t : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy first))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy second))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy direct)))
  (p : E ⟶ B) {a' b' c' : U ⟶ B}
  (first' : SSet.Homotopy a' b') (second' : SSet.Homotopy b' c')
  (direct' : SSet.Homotopy a' c')
  (hf : first'.h = first.h ≫ p) (hs : second'.h = second.h ≫ p)
  (hd : direct'.h = direct.h ≫ p)

/-- 元の全三角形の同じ後合成を、指定した三円柱の全三面で表示する。 -/
def familyCompStructImage : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy first'))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy second'))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy direct')) := by
  refine SSet.Edge.CompStruct.mk
    (SSet.yonedaEquiv (curry (familyCompStructRealization t ≫ p))) ?_ ?_ ?_
  · rw [familyTriangleCurry_face, ← Category.assoc, familyCompStructRealization_first, ← hf]
    rfl
  · rw [familyTriangleCurry_face, ← Category.assoc, familyCompStructRealization_second, ← hs]
    rfl
  · rw [familyTriangleCurry_face, ← Category.assoc, familyCompStructRealization_direct, ← hd]
    rfl

/-- 三面の表示を移しても、全実二単体は元の同じ全後合成そのもの。 -/
lemma familyCompStructImage_map :
    familyCompStructRealization (familyCompStructImage t p first' second' direct' hf hs hd) =
      familyCompStructRealization t ≫ p := by
  change uncurry (SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (curry (familyCompStructRealization t ≫ p)))) = _
  rw [Equiv.symm_apply_apply, uncurry_curry]

end SerrePositivity.KST.SConstruction
