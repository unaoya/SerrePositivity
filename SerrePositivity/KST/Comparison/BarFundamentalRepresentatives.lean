module

public import SerrePositivity.InfinityCategories.HA.Section4_1_2.BarVertexInclusion
public import SerrePositivity.KST.Comparison.GroupCompletionVertexEvaluation
public import SerrePositivity.KST.Spectra.SphereMappingComponents

/-!
# bar の基本群における標準比較の代表

概要：標準群完備化写像の円の代表と零次モノイドの nerve の辺の代表を同定する。
方針：円からの写像を区間へ引き戻し、恒等一次単体で評価する。
規約：Segal 1974 Proposition 1.5、KST Lemma 2.13 の標準比較の代表を保持する。
使われ方：基本群の積の反乗法性を連結成分の比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：零次モノイドの nerve から Kan 置換した bar への標準射。
方針：対角 bar への退化の射に Kan 置換の単位を合成する。
規約：基点は bar の唯一の頂点の像。
使われ方：基本群の元を表す一次単体の写像。
-/
def monoidVertexNerveKanMap (M : SimplicialObject MonCat.{u}) :
    nerve (SingleObj (M.obj (op ⦋0⦌))) ⟶ (monoidBarKanPointed M).right :=
  monoidVertexNerveMap M ≫ AnodyneKanReplacement.unit.app (monoidBar M)

/--
概要：零次モノイドの nerve から Kan な bar への射は基点を保存する。
方針：置換前の基点保存と ofVertex の基点の計算を使う。
規約：K-L9 のホモトピー類の基点と一致させる。
使われ方：基本群の辺の代表の後合成。
-/
theorem monoidVertexNerveKanMap_point (M : SimplicialObject MonCat.{u}) :
    (monoidVertexNerveKanMap M).app (op ⦋0⦌) (monoidNervePoint (M.obj (op ⦋0⦌))) =
      (monoidBarKanPointed M).basepoint := by
  calc
    _ = (AnodyneKanReplacement.unit.app (monoidBar M)).app (op ⦋0⦌)
        (monoidBarBasepoint M) := congrArg
      ((AnodyneKanReplacement.unit.app (monoidBar M)).app (op ⦋0⦌))
      (monoidVertexNerveMap_point M)
    _ = _ := (PointedSimplicialSet.basepoint_ofVertex _ _).symm

/--
概要：零次の元に対応する Kan な bar の境界定数一次単体。
方針：nerve の辺を標準射で後合成する。
規約：辺の正向きを用いる。
使われ方：円の写像空間の成分と基本群の積との比較。
-/
def monoidBarVertexLoop (M : SimplicialObject MonCat.{u}) (a : M.obj (op ⦋0⦌)) :
    (monoidBarKanPointed M).right.PtSimplex 1 (monoidBarKanPointed M).basepoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (monoidVertexNerveKanMap M) (monoidVertexNerveKanMap_point M)
    (monoidNerveLoop (M.obj (op ⦋0⦌)) a)

/--
概要：標準群完備化写像の頂点の円の代表は nerve の辺の代表に一致する。
方針：区間評価の式を使い、Yoneda の恒等一次単体で比較する。
規約：単位や積の類を後から任意に選び直さない。
使われ方：π₀ 上の標準比較の反乗法性。
-/
theorem groupCompletionVertex_eq_barLoop (M : SimplicialObject MonCat.{u})
    (a : M.obj (op ⦋0⦌)) :
    Spectra.SphereSimplex.equiv (monoidBarKanPointed M) 1
      (Spectra.PointedMapping.familyMap PointedSimplicialSet.circle (monoidBarKanPointed M)
        ((monoidGroupCompletionMap M).app _ a)) = monoidBarVertexLoop M a := by
  apply RelativeMorphism.ext
  rw [groupCompletionVertex_simplex_map]
  change (Spectra.PointedMapping.zeroSection (Δ[1] : SSet.{u}) ≫
    (Δ[1] : SSet.{u}) ◁ yonedaEquiv.symm a ≫
      (β_ (Δ[1] : SSet.{u}) (monoidSpace M)).hom ≫ monoidBarEdgeMap M) ≫
        AnodyneKanReplacement.unit.app (monoidBar M) =
    (yonedaEquiv.symm (monoidEdgeSimplex (M.obj (op ⦋0⦌)) a) ≫ monoidVertexNerveMap M) ≫
      AnodyneKanReplacement.unit.app (monoidBar M)
  congr 1
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp]
  rw [Equiv.apply_symm_apply]
  rw [monoidVertexNerveMap_edge]
  rfl

end SerrePositivity.KST.Comparison
