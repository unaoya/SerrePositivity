module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeEdgeCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback

/-! # 四角形の指定辺と join 錐の脚

概要：四角形を join 錐に直しても左辺と下辺は元の辺である。
方針：錐の二三角形の最初の辺を有限順序写像として計算する。
規約：左下 (0,0) が錐の頂点。使われ方：D6a の指定した四辺の固定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 概要：四角形の下辺は (t,0) である。
方針：第一座標を恒等、第二座標を始点とする。
規約：向きは左下から右下。使われ方：fiber 列の第一射の第一成分。 -/
def derivedSquareBottomEdge : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  CartesianMonoidalCategory.lift (𝟙 Δ[1]) (SSet.const (stdSimplex.obj₀Equiv.symm 0))

/-- 概要：四角形の左辺は (0,t) である。
方針：第一座標を始点、第二座標を恒等とする。
規約：向きは左下から左上。使われ方：fiber 列の第一射の第二成分。 -/
def derivedSquareLeftEdge : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  CartesianMonoidalCategory.lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 Δ[1])

/-- 概要：下側三角形の最初の辺は下辺である。
方針：Yoneda で二つの座標の有限計算に帰着する。
規約：面は δ₂。使われ方：指定した下辺との一致。 -/
lemma derivedSquareTriangle_bottom :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 1 = derivedSquareBottomEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 概要：上側三角形の最初の辺は左辺である。
方針：Yoneda で二つの座標の有限計算に帰着する。
規約：面は δ₂。使われ方：指定した左辺との一致。 -/
lemma derivedSquareTriangle_left :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 0 = derivedSquareLeftEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

private lemma join_first_edge :
    stdSimplex.δ (2 : Fin 3) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 1).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.δ (1 : Fin 2)) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom).1
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：cospan の左頂点への join 錐の脚は四角形の下辺に写る。
方針：最初の辺の join での計算と錐の下側三角形の同定を合成する。
規約：cospan の左は右下の頂点。使われ方：比較錐の第一脚の固定。 -/
lemma derivedCospanLeg_bottom :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.δ 1 ≫ horn₂₂.ι₀₂) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom =
        derivedSquareBottomEdge := by
  have h : stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.δ 1 ≫ horn₂₂.ι₀₂) := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft]
    rw [← Category.assoc, join_first_edge, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
  rw [← Category.assoc, ← h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_left,
    derivedSquareTriangle_bottom]

/-- 概要：cospan の右頂点への join 錐の脚は四角形の左辺に写る。
方針：最初の辺の join での計算と錐の上側三角形の同定を合成する。
規約：cospan の右は左上の頂点。使われ方：比較錐の第二脚の固定。 -/
lemma derivedCospanLeg_left :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.δ 1 ≫ horn₂₂.ι₁₂) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom =
        derivedSquareLeftEdge := by
  have h : stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.δ 1 ≫ horn₂₂.ι₁₂) := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight]
    rw [← Category.assoc, join_first_edge, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
  rw [← Category.assoc, ← h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_right,
    derivedSquareTriangle_left]

/-- 概要：四角形を錐に直した第一脚の一単体は指定した下辺である。
方針：join 錐の脚の式と有限幾何の同定を評価する。
規約：四角形の極限性は不要。使われ方：Hⁱ と元の下辺の一致。 -/
lemma derivedConeLeg_pullback_bottom {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F)
      (SSet.yonedaEquiv (stdSimplex.δ 1 ≫ horn₂₂.ι₀₂))).edge =
        SSet.yonedaEquiv (derivedSquareBottomEdge ≫ F) := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm (SSet.yonedaEquiv _)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ F) = _
  rw [Equiv.symm_apply_apply]
  have h := congrArg (fun k => k ≫ F) derivedCospanLeg_bottom
  simp only [Category.assoc] at h
  exact congrArg SSet.yonedaEquiv h

/-- 概要：四角形を錐に直した第二脚の一単体は指定した左辺である。
方針：join 錐の脚の式と有限幾何の同定を評価する。
規約：四角形の極限性は不要。使われ方：Hⁱ と元の左辺の一致。 -/
lemma derivedConeLeg_pullback_left {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F)
      (SSet.yonedaEquiv (stdSimplex.δ 1 ≫ horn₂₂.ι₁₂))).edge =
        SSet.yonedaEquiv (derivedSquareLeftEdge ≫ F) := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm (SSet.yonedaEquiv _)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ F) = _
  rw [Equiv.symm_apply_apply]
  have h := congrArg (fun k => k ≫ F) derivedCospanLeg_left
  simp only [Category.assoc] at h
  exact congrArg SSet.yonedaEquiv h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
