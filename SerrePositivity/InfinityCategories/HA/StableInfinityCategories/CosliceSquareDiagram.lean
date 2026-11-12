module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceCoconeDiagramEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingPiZero
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonExt

/-! # 固定した span 上の余錐の四角形表示

概要：coslice の余錐を四角形の関手単体集合へ写し、span 制限と終端頂点評価を比較する。
方針：余錐の形状と正方形の同型で前合成し、二つの評価の形状を同定する。
規約：span は厳密に固定する。使われ方：余極限の比較と suspension の標準比較の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：固定した span の余錐を四角形の図式へ写す。
方針：coslice の図式表示を余錐形状と正方形の同型の逆で制限する。
規約：値域に充填性を仮定しない。使われ方：coslice の比較射の四角形表示。 -/
def cosliceSquareDiagramMap {X : SSet.{u}} (p : (horn 2 0 : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p ⟶ (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCoconeDiagramMap p ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv).app X

/-- 概要：一般の余錐の四角形表示の頂点は形状同型の逆で前合成した図式。
方針：余錐図式の零次成分を前合成する。
規約：余錐の余極限性は不要。使われ方：固定図式の表示を変更した余錐の照合。 -/
lemma cosliceSquareDiagramMap_vertex {X : SSet.{u}} (p : (horn 2 0 : SSet.{u}) ⟶ X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    (cosliceSquareDiagramMap p).app (Opposite.op ⦋0⦌) c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫ c.val) := by
  change ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv).app X).app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCoconeDiagramMap p).app (Opposite.op ⦋0⦌) c) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCoconeDiagramMap_vertex]
  rfl

/-- 概要：押し出し四角形の余錐の四角形表示は元の四角形の関手頂点表示。
方針：余錐の零次表示と形状同型の逆射の合成を計算する。
規約：四角形の押し出し性は不要。使われ方：比較の始点・終点の同定。 -/
lemma cosliceSquareDiagramMap_pushoutCocone {X : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (cosliceSquareDiagramMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone R) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R := by
  change ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv).app X).app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCoconeDiagramMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone R)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCoconeDiagramMap_vertex]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ R)) = _
  rw [Iso.inv_hom_id_assoc]

/-- 概要：coslice の四角形表示を span に制限すると元の余錐図式の制限になる。
方針：形状の前合成の合成則と、同型で表した span の包含を使う。
規約：単体集合の射の厳密な等号。使われ方：比較が元の span を固定することの検査。 -/
lemma cosliceSquareDiagramMap_restriction {X : SSet.{u}}
    (p : (horn 2 0 : SSet.{u}) ⟶ X) :
    cosliceSquareDiagramMap p ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCoconeDiagramMap p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (horn 2 0 : SSet.{u}) X := by
  unfold cosliceSquareDiagramMap _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction
  rw [Category.assoc, ← NatTrans.comp_app, ← pre_map]
  congr 2
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 概要：正方形の終端頂点を余錐形状へ戻すと余錐頂点になる。
方針：逆形状を四角形とみなし、押し出し余錐の頂点の既存の計算則を使う。
規約：形状だけの等号。使われ方：coslice の終点射影と四角形の頂点評価の一致。 -/
lemma spanCoconeSquareIso_inv_terminalVertex :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (horn 2 0 : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 0) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pushoutCocone_vertex _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (horn 2 0 : SSet.{u}) Δ[0] ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv)) = _ at h
  rw [Iso.hom_inv_id, Category.comp_id] at h
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv 1 1 = _
  have hv : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    have ha := ((stdSimplex.obj₀Equiv.symm (0 : Fin 1)) i).isLt
    have hb := ((SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) i).isLt
    omega
  rw [hv, ← SSet.yonedaEquiv_comp, Category.id_comp]
  exact h.symm

/-- 概要：coslice の四角形表示の終端頂点での評価は元の終点射影。
方針：前合成の評価と形状の終端頂点を照合し、余錐図式の評価の式を使う。
規約：値域に追加仮定なし。使われ方：colimitVertexIso と四角形の比較の終点成分の同定。 -/
lemma cosliceSquareDiagramMap_targetEvaluation {X : SSet.{u}}
    (p : (horn 2 0 : SSet.{u}) ⟶ X) :
    cosliceSquareDiagramMap p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p := by
  rw [cosliceSquareDiagramMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt,
    spanCoconeSquareIso_inv_terminalVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCoconeDiagramMap_vertexEvaluation]

/-- 概要：coslice の四角形表示は指定された span に厳密に固定される。
方針：span 制限の式を余錐図式の固定条件と合成する。
規約：全単体での定値性。使われ方：比較図式の始点成分の恒等性。 -/
lemma cosliceSquareDiagramMap_fixed {X : SSet.{u}} (p : (horn 2 0 : SSet.{u}) ⟶ X) :
    cosliceSquareDiagramMap p ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) := by
  rw [cosliceSquareDiagramMap_restriction, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCoconeDiagramMap_restriction]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
