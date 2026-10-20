module
public import SerrePositivity.InfinityCategories.Derived.DGPinchedFamilyComposition
public import SerrePositivity.InfinityCategories.Derived.ConstantFunctorImageInvertible
public import SerrePositivity.InfinityCategories.Derived.DGQuotientLocalizingEdges

/-!
概要：指定実閉辺の定数族を照合し、反転関手の下での可逆性を得る。
方針：任意単体集合の定数族の計算を同じ実閉辺へ適用する。
規約：パラメータの有限性を仮定しない。使われ方：屋根評価族の合成分母の消去。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
/-- 実閉辺の定数族は、その同じ実辺を定値関手へ送ったものに一致する。 -/
lemma dgPinchedFamilyHom_closed {K : SSet.{max u v}} {x y : D}
    (d : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y) :
    dgPinchedFamilyHom A D (SSet.const (X := K) (pinchedClosedVertex A D d)) =
      constantFunctorHomMap K (Truncated.HomotopyCategory.homMk (dgClosedEdge A D d)) := by
  exact pinchedFamilyHom_const_vertex (K := K) (X := dgNerve A D) (pinchedClosedVertex A D d)
/-- 反転関手は、実閉分母の全パラメータ定数族も可逆にする。 -/
lemma dgInvertingFamilyDenominator_isIso {K : SSet.{max u v}} {Y : SSet.{max u v}}
    (P : Set D) (F : dgNerve A D ⟶ Y) (hF : InvertsEdges F (dgVerdierEdges A D P))
    {x y : D} (d : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y)
    (hd : (dgClosedEdge A D d).edge ∈ dgVerdierEdges A D P) :
    IsIso ((hoFunctor.map ((ihom K).map F)).toFunctor.map
      (dgPinchedFamilyHom A D (SSet.const (X := K) (pinchedClosedVertex A D d)))) := by
  rw [dgPinchedFamilyHom_closed]
  have he : IsIso ((hoFunctor.map F).toFunctor.map
      (Truncated.HomotopyCategory.homMk (dgClosedEdge A D d))) := by
    exact (isInvertibleEdge_congr (e := (edgeOfSimplex (dgClosedEdge A D d).edge).map
      ((truncation 2).map F)) (f := (dgClosedEdge A D d).map ((truncation 2).map F)) rfl).mp (hF hd)
  exact constantFunctorHomMap_image_isIso (K := K) F
    (Truncated.HomotopyCategory.homMk (dgClosedEdge A D d))

end SerrePositivity.InfinityCategories
