module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeIso

/-! # ホモトピー可逆な終点射による実四角形の移送
概要：ホモトピー圏で可逆な同じ閉加群射で、実四角形の終点を移す。
方針：元の coslice 比較辺の射影を同じ閉射に照合し、可逆性を反映する。
規約：span と二つの二単体を保持。使われ方：実二軸 Yoneda cofiber 四角形。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] [Small.{u} D]
  {W X Y Z T : ModuleCategory R D}
  (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData R D W X Y Z) (q : Z ⟶ T)

/-- ホモトピー可逆な閉射の同じ coslice 比較辺は可逆である。 -/
lemma dgModuleSquare_postcomposeSliceEdge_invertible
    (hq : IsIso ((moduleToHomotopy R D).map q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square)) (s.postcomposeSliceEdge q) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_isIso_of_homotopy R D q hq
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R D q).toTruncated :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso
      (SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R D q).toTruncated)
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D)
    (s.postcomposeSliceEdge_projection q)).mpr he
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square)) (s.postcomposeSliceEdge q) hp

/-- 同じホモトピー可逆な終点射による、実四角形全体の関手同型。 -/
def dgModuleSquare_postcomposeHomotopyFunctorIso
    (hq : IsIso ((moduleToHomotopy R D).map q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso s.square (s.postcompose q).square := by
  have := dgModuleSquare_postcomposeSliceEdge_invertible s q hq
  let e := asIso (SSet.Truncated.HomotopyCategory.homMk (s.postcomposeSliceEdge q))
  let t := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFunctorIsoOfVertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone s.square) (s.postcomposeCocone q) e).precomp
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone s.square).val = s.square := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ s.square) = _
    rw [Iso.inv_hom_id_assoc]
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫ (s.postcomposeCocone q).val = (s.postcompose q).square := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ (s.postcompose q).square) = _
    rw [Iso.inv_hom_id_assoc]
  exact (h₀ ▸ h₁ ▸ t)

/-- 同じホモトピー可逆な終点射による後合成は、実押し出し性を保つ。 -/
lemma dgModuleSquare_isPushout_postcompose_homotopy
    (hq : IsIso ((moduleToHomotopy R D).map q)) (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare s.square) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (s.postcompose q).square :=
  hs.of_functorIso (dgModuleSquare_postcomposeHomotopyFunctorIso s q hq)

end SerrePositivity.KST.SConstruction
