module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality

/-!
概要：同じ関手同型の前後合成を、内部 Hom の同じ合成射による像へ戻す。
方針：前後合成のホモトピー圏の作用と頂点同型の合成則を使う。
規約：元の指定値を保持。使われ方：a6 の fiber 比較の全作用による像の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の関手同型の後合成は、同じ内部 Hom の射による指定値の像。 -/
lemma functorIso_postcomp_vertexMap_heq {X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) (q : Y ⟶ Z) :
    HEq (e.postcomp q) (VertexIso.map e ((ihom X).map q)) := by
  rw [functorIso_postcomp_eq_mapIso]
  simp only [VertexIso.map, hoFunctor_map, Functor.toCatHom_toFunctor]
  rfl

/-- 同じ内部 Hom の合成作用の像は、元の関手同型の前後合成と値まで一致する。 -/
lemma functorIso_whisker_vertexMap_heq {A X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) (a : A ⟶ X) (v : Y ⟶ Z) :
    HEq (VertexIso.map e ((pre a).app Y ≫ (ihom A).map v))
      ((e.postcomp v).precomp a) := by
  rw [← vertexIso_map_comp]
  rw [← functorIso_precomp_postcomp]
  simp only [VertexIso.map, hoFunctor_map, Functor.toCatHom_toFunctor,
    functorIso_precomp_eq_mapIso, functorIso_postcomp_eq_mapIso]
  rfl

end SerrePositivity.InfinityCategories.F2
