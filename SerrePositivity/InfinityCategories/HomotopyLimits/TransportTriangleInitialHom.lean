module

public import SerrePositivity.InfinityCategories.HomotopyLimits.TransportTriangleHomFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramHomFamily

/-!
概要：同じ実際の輸送三角形の全 Hom の族を、始対象からの Hom 比較へ接続する。
方針：三角形全体の族を元の始点へ制限し、同じ終点を保つ中間 Hom の比較を適用する。
規約：底の二単体と全 Hom パラメータを保つ。終点の余極限性は仮定しない。
使われ方：共通余錐の始対象における、指定輸送三角形と native な全 Hom 係数の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
  {a b c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c} {g : B.Edge a c}
  (σ : SSet.Edge.CompStruct e f g) (v : (vertexFiber p a) _⦋0⦌) (y : B _⦋0⦌)
local notation "dᵀ" => transportTriangleTerminalVertex p (e := e) (f := f) v

/-- 実際の三角形全体を通した、元の始点からの中間 Hom の族。 -/
def transportTriangleInitialHomFamily :
    pinchedHomLeft (p.app (Opposite.op ⦋0⦌) dᵀ) y ⟶ leftFibrationInitialTotal p v.val y :=
  initialDiagramHomFamily p v.val (coherentTransportTriangleVertex p σ v)
    (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3))
    (coherentTransportTriangleVertex_initial p σ v) y (transportTriangleHomFamily p σ v y)
    (transportTriangleHomFamily_fixed p σ v y)

/-- 同じ三角形の中間 Hom の評価は、元の終点の全 Hom の族を厳密に回収する。 -/
lemma transportTriangleInitialHomFamily_evaluation :
    transportTriangleInitialHomFamily p σ v y ≫ leftFibrationInitialEvaluation p v.val y =
      leftFibrationPointHomFamily p dᵀ y := by
  rw [transportTriangleInitialHomFamily, initialDiagramHomFamily_evaluation]
  apply vertexFiber_hom_ext p y
  rw [vertexFiberLift_ι, transportTriangleHomFamily_endpoint]

private lemma transportTriangleHomFamily_endpointLift :
    vertexFiberLift p y
      (transportTriangleHomFamily p σ v y ≫
        sliceUnderProjection (coherentTransportTriangleVertex p σ v))
      (transportTriangleHomFamily_fixed p σ v y) = leftFibrationPointHomFamily p dᵀ y := by
  apply vertexFiber_hom_ext p y
  rw [vertexFiberLift_ι, transportTriangleHomFamily_endpoint]

variable (hv : IsInitialVertex v.val)

/-- 同じ中間 Hom の比較円柱と、元の終点の評価を全時刻で固定する条件。 -/
structure TransportTriangleInitialHomComparison where
  homotopy : SSet.Homotopy
    (leftFibrationPointHomFamily p dᵀ y ≫ leftFibrationInitialSection p v.val hv y)
    (transportTriangleInitialHomFamily p σ v y)
  evaluation : homotopy.h ≫ leftFibrationInitialEvaluation p v.val y =
    fst (pinchedHomLeft (p.app (Opposite.op ⦋0⦌) dᵀ) y) Δ[1] ≫
      leftFibrationPointHomFamily p dᵀ y

/-- 元の全 Hom の族の評価を固定する、同じ実際の三角形の比較円柱を選ぶ。 -/
def transportTriangleInitialHomComparison : TransportTriangleInitialHomComparison p σ v y hv :=
  Classical.choice (by
    obtain ⟨H, hH⟩ := initialDiagramHomFamily_section_homotopy p v.val
      (coherentTransportTriangleVertex p σ v)
      (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3))
      (coherentTransportTriangleVertex_initial p σ v) y (transportTriangleHomFamily p σ v y)
      (transportTriangleHomFamily_fixed p σ v y) hv
    refine ⟨⟨{ h := H.h
               h₀ := by
                 change SSet.ι₀ ≫ H.h = leftFibrationPointHomFamily p dᵀ y ≫
                   leftFibrationInitialSection p v.val hv y
                 simpa only [transportTriangleHomFamily_endpointLift] using H.h₀
               h₁ := by
                 change SSet.ι₁ ≫ H.h = transportTriangleInitialHomFamily p σ v y
                 exact H.h₁
               rel := by
                 apply SSet.hom_ext
                 intro n
                 apply ConcreteCategory.hom_ext
                 intro z
                 exact False.elim z.1.property }, ?_⟩⟩
    simpa only [transportTriangleHomFamily_endpointLift] using hH)

/-- 評価固定の同じ円柱から作る、元の全 Hom 比較の実際のホモトピー。 -/
def transportTriangleInitialHomComparisonHomotopy : SSet.Homotopy
    (leftFibrationPointHomFamily p dᵀ y ≫ leftFibrationInitialHomComparison p v.val hv y)
    (transportTriangleInitialHomFamily p σ v y ≫ leftFibrationInitialProjection p v.val y ≫
      (leftFibrationInitialBaseIso p v.val y).hom) := by
  simpa only [Category.assoc, leftFibrationInitialHomComparison] using
    functorHomotopyPostcomp (transportTriangleInitialHomComparison p σ v y hv).homotopy
      (leftFibrationInitialProjection p v.val y ≫ (leftFibrationInitialBaseIso p v.val y).hom)

/-- 公開した比較ホモトピーの円柱は、評価固定の元の中間円柱の像そのもの。 -/
lemma transportTriangleInitialHomComparisonHomotopy_projection :
    (transportTriangleInitialHomComparisonHomotopy p σ v y hv).h =
      (transportTriangleInitialHomComparison p σ v y hv).homotopy.h ≫
        leftFibrationInitialProjection p v.val y ≫ (leftFibrationInitialBaseIso p v.val y).hom :=
  rfl

/-- 始点が始対象なら、元の全 Hom の族の Hom 比較は同じ三角形を通した比較とホモトピック。 -/
lemma transportTriangleInitialHomComparison_homotopy :
    Nonempty (SSet.Homotopy
      (leftFibrationPointHomFamily p dᵀ y ≫ leftFibrationInitialHomComparison p v.val hv y)
      (transportTriangleInitialHomFamily p σ v y ≫ leftFibrationInitialProjection p v.val y ≫
        (leftFibrationInitialBaseIso p v.val y).hom)) :=
  ⟨transportTriangleInitialHomComparisonHomotopy p σ v y hv⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
