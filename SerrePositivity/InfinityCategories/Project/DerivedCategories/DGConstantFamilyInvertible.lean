module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPinchedFamilyComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ConstantFunctorImageInvertible
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientLocalizingEdges

/-!
概要：指定実閉辺の定数族を照合し、反転関手の下での可逆性を得る。
方針：任意単体集合の定数族の計算を同じ実閉辺へ適用する。
規約：パラメータの有限性を仮定しない。使われ方：屋根評価族の合成分母の消去。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
/-- 実閉辺の定数族は、その同じ実辺を定値関手へ送ったものに一致する。 -/
lemma dgPinchedFamilyHom_closed {K : SSet.{max u v}} {x y : D}
    (d : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D d)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D d)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilyHom_const_vertex (K := K) (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D d)
/-- 反転関手は、実閉分母の全パラメータ定数族も可逆にする。 -/
lemma dgInvertingFamilyDenominator_isIso {K : SSet.{max u v}} {Y : SSet.{max u v}}
    (P : Set D) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P))
    {x y : D} (d : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
    (hd : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D d).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    IsIso ((hoFunctor.map ((ihom K).map F)).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D d)))) := by
  rw [dgPinchedFamilyHom_closed]
  have he : IsIso ((hoFunctor.map F).toFunctor.map
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D d))) := by
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D d).edge).map
      ((truncation 2).map F)) (f := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D d).map ((truncation 2).map F)) rfl).mp (hF hd)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.constantFunctorHomMap_image_isIso (K := K) F
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D d))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
