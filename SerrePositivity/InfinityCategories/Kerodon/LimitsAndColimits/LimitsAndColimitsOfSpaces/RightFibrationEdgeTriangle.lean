module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.EdgeTrianglePrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationIntervalProjection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationInitialDiagramSpan
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.MappingParameters
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.FirstVertexLeftAnodyne

/-!
概要：共通 span の辺形状 Δ[1] 上の実三角形族と、その三面の照合。
方針：元の同じ実錐を底へ送り、端点制限と独立した区間比較の式を使う。
規約：一般の図式形状には拡張しない。選択した切断は元のまま使う。
使われ方：β_native と標準後合成の全族の同定の三面。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions IsomorphismsAndIsofibrations MorphismSpaces LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：辺の同じ実錐の全族を底へ送って得る実三角形族。
方針：辺形状の prism と元の錐の展開を合成する。
規約：別の錐を選ばない。使われ方：共通 span の三面。 -/
def rightFibrationEdgeTriangleFamily {A E B : SSet.{u}} (r : E ⟶ B)
    (e : (Δ[1] : SSet.{u}) ⟶ E) (x : B _⦋0⦌)
    (f : A ⟶ rightFibrationMappingDiagramTotal r e x) :
    A ⊗ (Δ[2] : SSet.{u}) ⟶ B :=
  edgeTrianglePrism A ≫ sliceOverUncurry
    (f ≫ vertexFiberι (sliceOverProjection e ≫ r) x) ≫ r

/-- 概要：三角形の第一面・長辺は、同じ端点への元の Hom 射影の区間像。
方針：prism の面、正規化した錐制限、独立した区間比較の等式を順に使う。
規約：i=1 が第一面、i=0 が長辺。使われ方：選択した共通切断の三面の照合。 -/
lemma rightFibrationEdgeTriangleFamily_side {A E B : SSet.{u}}
    (r : E ⟶ B) (e : (Δ[1] : SSet.{u}) ⟶ E) (x : B _⦋0⦌)
    (f : A ⟶ rightFibrationMappingDiagramTotal r e x) (i : Fin 2)
    (c : E _⦋0⦌) (hc : stdSimplex.δ i ≫ e = SSet.yonedaEquiv.symm c) :
    (A ◁ stdSimplex.δ i.succ) ≫ rightFibrationEdgeTriangleFamily r e x f =
      (intervalFamilyHomotopy
        (f ≫ rightFibrationMappingDiagramRestriction r e (stdSimplex.δ i) hc x ≫
          rightFibrationMappingHomProjection r c x ≫
            pinchedHomToIntervalMappingSpace x (r.app _ c))).h := by
  have hf : sliceOverUncurry
      ((f ≫ rightFibrationMappingDiagramRestriction r e (stdSimplex.δ i) hc x) ≫
        vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ r) x) =
      joinMap (𝟙 A) (stdSimplex.δ i) ≫
        sliceOverUncurry (f ≫ vertexFiberι (sliceOverProjection e ≫ r) x) := by
    rw [Category.assoc, rightFibrationMappingDiagramRestriction_ι, ← Category.assoc,
      normalizedConeRestriction_uncurry]
  have hi := rightFibrationMappingHomProjection_intervalUncurry r c x
    (f ≫ rightFibrationMappingDiagramRestriction r e (stdSimplex.δ i) hc x)
  rw [hf] at hi
  unfold rightFibrationEdgeTriangleFamily
  rw [← Category.assoc, edgeTrianglePrism_side]
  simpa only [intervalFamilyHomotopy, Category.assoc] using
    congrArg ((β_ A (Δ[1] : SSet.{u})).hom ≫ ·) hi.symm

/-- 概要：第二面は、同じ指定辺をパラメータに関して定値にした族そのもの。
方針：錐の図式上の固定条件を使う。
規約：全パラメータの等式。使われ方：実三角形の合成則。 -/
lemma rightFibrationEdgeTriangleFamily_edge {A E B : SSet.{u}}
    (r : E ⟶ B) (e : (Δ[1] : SSet.{u}) ⟶ E) (x : B _⦋0⦌)
    (f : A ⟶ rightFibrationMappingDiagramTotal r e x) :
    (A ◁ stdSimplex.δ (0 : Fin 3)) ≫ rightFibrationEdgeTriangleFamily r e x f =
      snd A (Δ[1] : SSet.{u}) ≫ e ≫ r := by
  unfold rightFibrationEdgeTriangleFamily
  rw [← Category.assoc, edgeTrianglePrism_edge]
  simpa only [Category.assoc] using congrArg (fun k =>
    snd A (Δ[1] : SSet.{u}) ≫ k ≫ r)
    (sliceOverUncurry_fixed
      (f ≫ vertexFiberι (sliceOverProjection e ≫ r) x))

/-- 概要：辺の最初の頂点の包含は left anodyne。
方針：既存の標準単体の始点包含に一致させる。
規約：面番号は 1。使われ方：共通 span の切断。 -/
lemma edgeInitialVertex_leftAnodyne :
    leftAnodyneExtensions (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
  have he : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
      SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [he]
  exact stdSimplex_firstVertex_leftAnodyne 1

variable {E B : SSet.{u}} [Quasicategory B] (r : E ⟶ B) [RightFibration r]
  (e : (Δ[1] : SSet.{u}) ⟶ E) (c : E _⦋0⦌)
  (hc : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm c) (x : B _⦋0⦌)

/-- 概要：共通 span の同じ全切断を使って得る辺上の実三角形族。
方針：既存の全切断を実三角形族へ適用する。
規約：元の選択を保持。使われ方：β_native の三面。 -/
def rightFibrationEdgeTriangle :
    Basic.pinchedHom x (r.app _ c) ⊗ (Δ[2] : SSet.{u}) ⟶ B :=
  rightFibrationEdgeTriangleFamily r e x
    (rightFibrationInitialDiagramSection r e (stdSimplex.δ (1 : Fin 2))
      edgeInitialVertex_leftAnodyne c hc x)

/-- 概要：選択した辺の三角形族の第一面は、元の pinched Hom の区間比較そのもの。
方針：独立した一点の比較を適用し、共通切断の射影が厳密に恒等であることを使う。
規約：頂点別の比較に弱めない。使われ方：標準の後合成との全族の同定。 -/
lemma rightFibrationEdgeTriangle_first :
    (Basic.pinchedHom x (r.app _ c) ◁ stdSimplex.δ (2 : Fin 3)) ≫
        rightFibrationEdgeTriangle r e c hc x =
      (intervalFamilyHomotopy (pinchedHomToIntervalMappingSpace x (r.app _ c))).h := by
  unfold rightFibrationEdgeTriangle
  have hface := rightFibrationEdgeTriangleFamily_side r e x
    (rightFibrationInitialDiagramSection r e (stdSimplex.δ (1 : Fin 2))
      edgeInitialVertex_leftAnodyne c hc x) (1 : Fin 2) c hc
  simp only [Fin.succ] at hface
  refine hface.trans ?_
  have hs := rightFibrationInitialDiagramSection_projection r e
    (stdSimplex.δ (1 : Fin 2)) edgeInitialVertex_leftAnodyne c hc x
  dsimp only [rightFibrationInitialDiagramProjection] at hs
  simpa only [Category.assoc, Category.id_comp] using congrArg
    (fun k => (intervalFamilyHomotopy
      (k ≫ pinchedHomToIntervalMappingSpace x (r.app _ c))).h) hs

/-- 概要：選択した全切断からの実三角形の第二面は、同じ指定辺の定値族。
方針：一般の錐族の第二面を適用する。
規約：面番号は 0。使われ方：標準後合成との照合。 -/
lemma rightFibrationEdgeTriangle_edge :
    (Basic.pinchedHom x (r.app _ c) ◁ stdSimplex.δ (0 : Fin 3)) ≫
        rightFibrationEdgeTriangle r e c hc x =
      snd (Basic.pinchedHom x (r.app _ c)) (Δ[1] : SSet.{u}) ≫ e ≫ r :=
  rightFibrationEdgeTriangleFamily_edge r e x _

/-- 概要：選択した全切断からの実三角形の長辺は、元の β_native の区間模型への像。
方針：同じ終点への錐制限と独立した区間比較を使う。
規約：面番号は 1。使われ方：標準後合成との全族比較。 -/
lemma rightFibrationEdgeTriangle_long (d : E _⦋0⦌)
    (hd : stdSimplex.δ (0 : Fin 2) ≫ e = SSet.yonedaEquiv.symm d) :
    (Basic.pinchedHom x (r.app _ c) ◁ stdSimplex.δ (1 : Fin 3)) ≫
        rightFibrationEdgeTriangle r e c hc x =
      (intervalFamilyHomotopy
        (rightFibrationInitialDiagramEndpointMap r e (stdSimplex.δ (1 : Fin 2))
          edgeInitialVertex_leftAnodyne c hc x (stdSimplex.δ (0 : Fin 2)) d hd ≫
            pinchedHomToIntervalMappingSpace x (r.app _ d))).h := by
  unfold rightFibrationEdgeTriangle
  have hface := rightFibrationEdgeTriangleFamily_side r e x
    (rightFibrationInitialDiagramSection r e (stdSimplex.δ (1 : Fin 2))
      edgeInitialVertex_leftAnodyne c hc x) (0 : Fin 2) d hd
  have hi : (0 : Fin 2).succ = (1 : Fin 3) := rfl
  rw [hi] at hface
  unfold rightFibrationInitialDiagramEndpointMap
  simp only [Category.assoc]
  exact hface

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
