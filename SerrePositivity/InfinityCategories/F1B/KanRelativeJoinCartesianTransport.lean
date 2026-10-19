module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeCosliceCancellation
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinCartesianRestriction
public import SerrePositivity.InfinityCategories.F1B.KanRelativeHomRestrictionInnerFibration

/-!
概要：相対 join の全空間で選んだ底への cartesian 輸送は制限射に関しても cartesian。
方針：制限による cartesian 辺の保存と合成射影の消去補題を使う。
規約：元の射は cocartesian fibration、底と値域は quasicategory。
使われ方：制限射の cartesian な持ち上げを fiber の持ち上げと組み立てる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：底への cartesian 辺は相対 join の制限射自体に関して cartesian。
方針：像の cartesian 性を既存の保存補題で示し、合成の消去則を適用する。
規約：この結論だけで制限射の cartesian fibration 性を主張しない。
使われ方：fiber 内の辺と底方向の辺を分けた cartesian 輸送の構成。 -/
lemma kanRelativeJoinRestriction_isCartesianEdge_of_projection {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (e : (kanFiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) D) _⦋1⦌)
    (he : IsCartesianEdge
      (kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D) e) :
    IsCartesianEdge (kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p)) e := by
  have : InnerFibration (kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p)) :=
    kanRelativeJoinRestriction_innerFibration p
  have : Quasicategory
      (kanFiberwiseHom (Over.mk (relativeJoinBaseProjection p (𝟙 C))).hom D) :=
    inferInstanceAs (Quasicategory (kanFiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) D))
  have : Quasicategory (kanFiberwiseHom (Over.mk p).hom D) :=
    inferInstanceAs (Quasicategory (kanFiberwiseHom p D))
  apply kanIsCartesianEdge_of_comp
    (kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p))
    (kanFiberwiseHomProjection p D) e
  · change IsCartesianEdge (kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p) ≫
      kanFiberwiseHomProjection (Over.mk p).hom D) e
    rw [kanFiberwiseHomPre_projection (D := D) (kanRelativeJoinInlOver p)]
    exact he
  · exact kanRelativeJoinRestriction_preservesCartesianEdges p e he

/-- 概要：底の任意の辺に沿い終点を指定して、制限射でも cartesian な輸送を選べる。
方針：底への cartesian fibration の持ち上げに合成射の消去を適用する。
規約：持ち上げた辺の制限像は指定せず、底への射影を指定する。
使われ方：任意の制限像の辺を底方向と fiber 方向に分解する第一段。 -/
lemma exists_kanRelativeJoinRestriction_cartesianTransport {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (x : (kanFiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) D) _⦋0⦌)
    (b : (Δ[1] : SSet.{u}) ⟶ C)
    (hb : stdSimplex.δ 0 ≫ b = SSet.yonedaEquiv.symm
      ((kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D).app
        (Opposite.op ⦋0⦌) x)) :
    ∃ a : (Δ[1] : SSet.{u}) ⟶ kanFiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) D,
      stdSimplex.δ 0 ≫ a = SSet.yonedaEquiv.symm x ∧
      a ≫ kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D = b ∧
      IsCartesianEdge (kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D)
        (SSet.yonedaEquiv a) ∧
      IsCartesianEdge (kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p))
        (SSet.yonedaEquiv a) := by
  obtain ⟨a, ha, hap, hac⟩ := CartesianFibration.mem
    (p := kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D) |>.2 x b hb
  exact ⟨a, ha, hap, hac, kanRelativeJoinRestriction_isCartesianEdge_of_projection p _ hac⟩

end SerrePositivity.InfinityCategories.F1B
