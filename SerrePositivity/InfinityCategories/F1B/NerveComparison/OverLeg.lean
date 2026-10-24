module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.OverIso
public import SerrePositivity.InfinityCategories.F1B.Cones.CoconeLegReverse
public import SerrePositivity.InfinityCategories.F1B.Cones.SliceDiagramConeMap
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.UnderCanonicalCone
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.OppositeVertices

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
lemma nerveOverRawSliceIso_vertex (x : Over c) :
    (SerrePositivity.InfinityCategories.F1B.nerveOverRawSliceIso c).hom.app (Opposite.op ⦋0⦌) (nerveVertex x) =
      SerrePositivity.InfinityCategories.F1B.coconeReverseCone (SerrePositivity.InfinityCategories.F1B.nerveUnderSimplex (op c)
        (nerveVertex (Under.mk x.hom.op))) := by
  rfl

/-- 概要：Over の頂点を表す錐の元の射を反転と前後合成で表示する。
方針：Under の零単体の反転と混合辺の公式を使う。
規約：元の Over の対象と構造射を保持する。
使われ方：B5 の左 Kan の標準余錐の同定。 -/
lemma nerveOverIso_vertex_val (x : Over c) :
    ((SerrePositivity.InfinityCategories.F1B.nerveOverIso c).hom.app (Opposite.op ⦋0⦌) (nerveVertex x)).val =
      joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.opIso ⦋0⦌).inv ≫
        (SerrePositivity.InfinityCategories.F1B.coconeReverseCone (SerrePositivity.InfinityCategories.F1B.nerveUnderSimplex (op c)
          (nerveVertex (Under.mk x.hom.op)))).val ≫ (SerrePositivity.InfinityCategories.F1B.nerveUnopIso C).hom := by
  dsimp only [SerrePositivity.InfinityCategories.F1B.nerveOverIso, Iso.trans_hom, asIso_hom]
  simp only [NatTrans.comp_app_apply]
  rw [SerrePositivity.InfinityCategories.F1B.sliceOver_cast_val]
  change joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.opIso ⦋0⦌).inv ≫
    ((SerrePositivity.InfinityCategories.F1B.nerveOverRawSliceIso c).hom.app (Opposite.op ⦋0⦌) (nerveVertex x)).val ≫ _ = _
  rw [nerveOverRawSliceIso_vertex]
  exact SerrePositivity.InfinityCategories.F1B.nerveOverBase_eq c

/-- 概要：Over の頂点を表す錐の脚は元の構造射に一致する。
方針：Under の零単体の反転と混合辺の公式を使う。
規約：元の Over の対象と構造射を保持する。
使われ方：B5 の左 Kan の標準余錐の同定。 -/
lemma nerveOverIso_leg (x : Over c) :
    ((SerrePositivity.InfinityCategories.F1B.nerveOverIso c).hom.app (Opposite.op ⦋0⦌) (nerveVertex x)).val.app (Opposite.op ⦋1⦌)
      (SerrePositivity.InfinityCategories.F1B.joinCoconeLegSimplex (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) =
        ComposableArrows.mk₁ x.hom := by
  rw [nerveOverIso_vertex_val]
  change (SerrePositivity.InfinityCategories.F1B.nerveUnopIso C).hom.app (Opposite.op ⦋1⦌)
    ((SerrePositivity.InfinityCategories.F1B.coconeReverseCone (SerrePositivity.InfinityCategories.F1B.nerveUnderSimplex (op c)
      (nerveVertex (Under.mk x.hom.op)))).val.app (Opposite.op ⦋1⦌)
        ((joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.opIso ⦋0⦌).inv).app (Opposite.op ⦋1⦌)
          (SerrePositivity.InfinityCategories.F1B.joinConeLegSimplex (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))))) = _
  rw [SerrePositivity.InfinityCategories.F1B.joinConeLegSimplex_natural]
  have hp : (stdSimplex.opIso.{u} ⦋0⦌).inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) =
        SSet.opObjEquiv.symm (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) := by
    apply SSet.opObjEquiv.injective
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    omega
  rw [hp, SerrePositivity.InfinityCategories.F1B.coconeReverseCone_leg]
  have hu : (SerrePositivity.InfinityCategories.F1B.nerveUnderSimplex (op c) (nerveVertex (Under.mk x.hom.op))).val.app
      (Opposite.op ⦋1⦌) (SerrePositivity.InfinityCategories.F1B.joinCoconeLegSimplex (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) =
        ComposableArrows.mk₁ x.hom.op := by
    change (sliceUnderUncurry (SerrePositivity.InfinityCategories.F1B.nerveUnderMap (op c))).app (Opposite.op ⦋1⦌)
      (SerrePositivity.InfinityCategories.F1B.coneLegSimplex (Under.mk x.hom.op)) = _
    exact SerrePositivity.InfinityCategories.F1B.nerveUnderUncurry_leg (op c) (Under.mk x.hom.op)
  rw [hu]
  exact SerrePositivity.InfinityCategories.F1B.nerveUnopIso_edge x.hom

end SerrePositivity.InfinityCategories.F1B
