module

public import SerrePositivity.InfinityCategories.F2.FiberwisePullbackNativeCone

/-!
概要：元の全空間 Kan 引き戻し極限錐と path 引き戻し錐の全比較円柱の二制限。
方針：指定頂点輸送の全境界式を左右へ制限する。
規約：頂点側は元の比較射の辺、図式側は元の cospan で全時刻定値。
使われ方：元の三射影を保持する native な引き戻し交換の錐比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {E D H B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
  [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)]

/-- 概要：元の全空間頂点の錐と元の path 引き戻し頂点の錐の全比較ホモトピー。
方針：指定頂点輸送が保持する元の全円柱。
規約：元の図式上の全錐。使われ方：比較射の三射影と native な錐の照合。 -/
def fiberwisePullbackNativeConeHomotopy :
    SSet.Homotopy (fiberwisePullbackNativeCone p f g).val
      (intervalPullbackCone (continuousKanMap f) (continuousKanMap g)).val :=
  (fiberwisePullbackNativeConeTransport p f g).homotopy

/-- 概要：全錐比較の頂点制限は元の Kan 比較射から作った指定円柱そのもの。
方針：頂点輸送の左制限。規約：厳密な射の等式。使われ方：元の比較射の保持。 -/
lemma fiberwisePullbackNativeConeHomotopy_apex :
    (joinInl _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (fiberwisePullbackNativeConeHomotopy p f g).h =
      (β_ (Δ[0] : SSet.{u + 1}) (Δ[1] : SSet.{u + 1})).hom ≫
        fiberwisePullbackComparisonApexPrism p f g :=
  (fiberwisePullbackNativeConeTransport p f g).apex

/-- 概要：全錐比較の元の cospan への制限は全時刻で定値。
方針：頂点輸送の右制限。規約：高次単体も固定。使われ方：同じ元の図式上の比較。 -/
lemma fiberwisePullbackNativeConeHomotopy_diagram :
    (joinInr _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (fiberwisePullbackNativeConeHomotopy p f g).h =
      fst _ (Δ[1] : SSet.{u + 1}) ≫
        kanDiagramCoherentNerve (kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)) :=
  (fiberwisePullbackNativeConeTransport p f g).diagram

/-- 概要：全錐比較の全垂直辺は可逆。
方針：指定境界の可逆性を全錐へ延長。規約：錐全体の同型。使われ方：極限性の輸送の証人。 -/
lemma fiberwisePullbackNativeConeHomotopy_vertical_isInvertible
    (x : (join _ _ : SSet.{u + 1}) _⦋0⦌) :
    IsInvertibleEdge
      (simplicialHomotopyVertexEdge (fiberwisePullbackNativeConeHomotopy p f g) x).toTruncated :=
  (fiberwisePullbackNativeConeTransport p f g).vertical_isInvertible x

end SerrePositivity.InfinityCategories.F2
