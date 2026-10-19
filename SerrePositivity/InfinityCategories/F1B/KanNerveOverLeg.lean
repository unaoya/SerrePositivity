module

public import SerrePositivity.InfinityCategories.F1B.KanNerveOverIso
public import SerrePositivity.InfinityCategories.F1B.KanCoconeLegReverse
public import SerrePositivity.InfinityCategories.F1B.KanSliceDiagramConeMap
public import SerrePositivity.InfinityCategories.F1B.KanNerveUnderCanonicalCone
public import SerrePositivity.InfinityCategories.F1B.KanNerveOppositeVertices

/-!
概要：Over の nerve と native な slice の比較が構造射を保つことを証明する。
方針：反対 Under の余錐の脚を反転し標的を元へ戻す。
規約：元の指定対象・構造射を保持する。
使われ方：B5 の指定単位の左 Kan 局所余錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet Opposite
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {C : Type u} [Category.{u} C] (c : C)


/-- 概要：Over の頂点の中間表示は反対の Under の余錐の反転。
方針：Under の零単体の反転と混合辺の公式を使う。
規約：元の Over の対象と構造射を保持する。
使われ方：B5 の左 Kan の標準余錐の同定。 -/
lemma kanNerveOverRawSliceIso_vertex (x : Over c) :
    (kanNerveOverRawSliceIso c).hom.app (Opposite.op ⦋0⦌) (nerveVertex x) =
      kanCoconeReverseCone (kanNerveUnderSimplex (op c)
        (nerveVertex (Under.mk x.hom.op))) := by
  rfl

/-- 概要：Over の頂点を表す錐の元の射を反転と前後合成で表示する。
方針：Under の零単体の反転と混合辺の公式を使う。
規約：元の Over の対象と構造射を保持する。
使われ方：B5 の左 Kan の標準余錐の同定。 -/
lemma kanNerveOverIso_vertex_val (x : Over c) :
    ((kanNerveOverIso c).hom.app (Opposite.op ⦋0⦌) (nerveVertex x)).val =
      joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.opIso ⦋0⦌).inv ≫
        (kanCoconeReverseCone (kanNerveUnderSimplex (op c)
          (nerveVertex (Under.mk x.hom.op)))).val ≫ (kanNerveUnopIso C).hom := by
  dsimp only [kanNerveOverIso, Iso.trans_hom, asIso_hom]
  simp only [NatTrans.comp_app_apply]
  rw [kanSliceOver_cast_val]
  change joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.opIso ⦋0⦌).inv ≫
    ((kanNerveOverRawSliceIso c).hom.app (Opposite.op ⦋0⦌) (nerveVertex x)).val ≫ _ = _
  rw [kanNerveOverRawSliceIso_vertex]
  exact kanNerveOverBase_eq c

/-- 概要：Over の頂点を表す錐の脚は元の構造射に一致する。
方針：Under の零単体の反転と混合辺の公式を使う。
規約：元の Over の対象と構造射を保持する。
使われ方：B5 の左 Kan の標準余錐の同定。 -/
lemma kanNerveOverIso_leg (x : Over c) :
    ((kanNerveOverIso c).hom.app (Opposite.op ⦋0⦌) (nerveVertex x)).val.app (Opposite.op ⦋1⦌)
      (kanJoinCoconeLegSimplex (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) =
        ComposableArrows.mk₁ x.hom := by
  rw [kanNerveOverIso_vertex_val]
  change (kanNerveUnopIso C).hom.app (Opposite.op ⦋1⦌)
    ((kanCoconeReverseCone (kanNerveUnderSimplex (op c)
      (nerveVertex (Under.mk x.hom.op)))).val.app (Opposite.op ⦋1⦌)
        ((joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.opIso ⦋0⦌).inv).app (Opposite.op ⦋1⦌)
          (kanJoinConeLegSimplex (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))))) = _
  rw [kanJoinConeLegSimplex_natural]
  have hp : (stdSimplex.opIso.{u} ⦋0⦌).inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) =
        SSet.opObjEquiv.symm (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) := by
    apply SSet.opObjEquiv.injective
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    omega
  rw [hp, kanCoconeReverseCone_leg]
  have hu : (kanNerveUnderSimplex (op c) (nerveVertex (Under.mk x.hom.op))).val.app
      (Opposite.op ⦋1⦌) (kanJoinCoconeLegSimplex (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) =
        ComposableArrows.mk₁ x.hom.op := by
    change (sliceUnderUncurry (kanNerveUnderMap (op c))).app (Opposite.op ⦋1⦌)
      (kanConeLegSimplex (Under.mk x.hom.op)) = _
    exact kanNerveUnderUncurry_leg (op c) (Under.mk x.hom.op)
  rw [hu]
  exact kanNerveUnopIso_edge x.hom

end SerrePositivity.InfinityCategories.F1B
