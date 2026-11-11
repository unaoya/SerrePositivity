module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Checks

/-! # 複体の射とホモトピーから dg nerve の辺・三角形を作る

概要：chain map を辺に、合成の差の次数 −1 原始元を合成三角形にする。
方針：閉零元と辺の既存の同値を使い、通常順合成を cochain 合成に同定する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：N7c の fiber 錐の標準二単体。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded CochainComplex HomComplex

variable {A : Type u} [CommRing A] {X Y Z : Complex A}

/-- 概要：複体の chain map を dg nerve の端点付き辺にする。
方針：chain map の閉零 cochain を辺と閉零元の同値で戻す。
規約：HA Example 1.3.1.8。使われ方：標準引き戻し錐の辺。 -/
def complexEdge (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) :=
  SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle ⟨Cochain.ofHom f, δ_ofHom f⟩)

/-- 概要：chain map から作る辺の閉零成分は元の chain map の cochain。
方針：辺と閉零元の同値の右逆則を評価する。
規約：HA Example 1.3.1.8。使われ方：合成三角形の方程式の読み替え。 -/
lemma complexEdge_cycle (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle (complexEdge f).toTruncated).val = Cochain.ofHom f := rfl

/-- 概要：合成の差の原始元は三つの指定した chain map の合成三角形を定める。
方針：N3 の三角形の構成へ cochain の微分等式を渡す。
規約：HA Example 1.3.1.8。使われ方：fiber のホモトピーから join 錐を作る。 -/
def complexCompStruct (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (t : Cochain X Z (-1)) (ht : δ (-1) 0 t = Cochain.ofHom (f ≫ g) - Cochain.ofHom h) :
    SSet.Edge.CompStruct (complexEdge f) (complexEdge g) (complexEdge h) := by
  apply SSet.Edge.CompStruct.ofTruncated
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compStructOfHomotopy _ _ _ t
  change δ (-1) 0 t = @Sub.sub (Cochain X Z 0) inferInstance
    (compose (D := Complex A) A (Cochain.ofHom g) (Cochain.ofHom f) rfl) (Cochain.ofHom h)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose, ← Cochain.ofHom_comp]
  exact ht

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
