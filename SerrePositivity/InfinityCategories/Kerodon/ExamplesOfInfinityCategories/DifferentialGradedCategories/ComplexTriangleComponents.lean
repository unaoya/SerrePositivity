module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComplexTriangles
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TripleHom

/-! # 複体の合成三角形の成分

概要：chain map とホモトピーから構成した三角形の対象・三辺・高次成分を計算する。
方針：N3 の三角形の構成の定義を評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：標準 fiber の錐の回収成分の同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded CochainComplex HomComplex

variable {A : Type u} [CommRing A] {X Y Z : Complex A}

/-- 概要：複体の合成三角形の対象族は元の三つの複体。
方針：三角形の対象の定義を評価する。
規約：HA Example 1.3.1.8。使われ方：錐の三つの頂点を固定する。 -/
lemma complexCompStruct_obj (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (t : Cochain X Z (-1)) (ht : δ (-1) 0 t = Cochain.ofHom (f ≫ g) - Cochain.ofHom h)
    (i : Fin 3) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct f g h t ht).simplex.obj i = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleObj X Y Z i := rfl

/-- 概要：複体の合成三角形の最初の辺の成分は最初の chain map。
方針：三角形の射族の二点分岐を評価する。
規約：HA Example 1.3.1.8。使われ方：錐の射 p・q の cochain を回収する。 -/
lemma complexCompStruct_edge01 (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (t : Cochain X Z (-1)) (ht : δ (-1) 0 t = Cochain.ofHom (f ≫ g) - Cochain.ofHom h) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct f g h t ht).simplex.toSimplexData.edgeHom 0 1 (by decide) =
      Cochain.ofHom f := rfl

/-- 概要：複体の合成三角形の最後の辺の成分は二番目の chain map。
方針：三角形の射族の二点分岐を評価する。
規約：HA Example 1.3.1.8。使われ方：cospan の射 g・h の cochain を回収する。 -/
lemma complexCompStruct_edge12 (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (t : Cochain X Z (-1)) (ht : δ (-1) 0 t = Cochain.ofHom (f ≫ g) - Cochain.ofHom h) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct f g h t ht).simplex.toSimplexData.edgeHom 1 2 (by decide) =
      Cochain.ofHom g := rfl

/-- 概要：複体の合成三角形の対角辺の成分は指定された第三の chain map。
方針：三角形の射族の二点分岐を評価する。
規約：HA Example 1.3.1.8。使われ方：共通の対角射 t の cochain を回収する。 -/
lemma complexCompStruct_edge02 (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (t : Cochain X Z (-1)) (ht : δ (-1) 0 t = Cochain.ofHom (f ≫ g) - Cochain.ofHom h) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct f g h t ht).simplex.toSimplexData.edgeHom 0 2 (by decide) =
      Cochain.ofHom h := rfl

/-- 概要：複体の合成三角形の三点成分は指定された次数 −1 のホモトピー。
方針：三角形の射族の三点分岐を評価する。
規約：HA Example 1.3.1.8。使われ方：標準 fiber のホモトピー u と零の v を回収する。 -/
lemma complexCompStruct_triple (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (t : Cochain X Z (-1)) (ht : δ (-1) 0 t = Cochain.ofHom (f ≫ g) - Cochain.ofHom h) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct f g h t ht).simplex.toSimplexData.tripleHom 0 1 2 (by decide) (by decide) =
      t := rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
