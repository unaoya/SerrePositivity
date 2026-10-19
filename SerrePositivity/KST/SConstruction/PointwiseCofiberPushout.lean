module
public import SerrePositivity.KST.SConstruction.PointwiseDiagramPushout
public import SerrePositivity.KST.SConstruction.GappedIso

/-! # cofiber 図式の C 内の点ごとの押し出し閉性
概要：cofiber 図式の span を C 内で押し出しても cofiber 図式となる。
方針：包含の完全性と同じ span の押し出しの比較を使う。
規約：新しい条件を仮定しない。使われ方：McCarthy の raw ρ の持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：cofiber 条件は正方形全体の関手同型で保たれる。
方針：零角と押し出し性を同じ同型で移す。
規約：頂点ごとの同型の族では代用しない。使われ方：点ごとの選択との比較。 -/
lemma IsCofiberDiagramVertex.of_vertexIso {C : SSet.{u}} [Quasicategory C]
    {v w : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) _⦋0⦌}
    (hv : IsCofiberDiagramVertex v) (e : VertexIso v w) : IsCofiberDiagramVertex w := by
  let F := squareDiagram v
  let G := squareDiagram w
  have hF : functorVertex F = v := (functorVertexEquiv _ C).apply_symm_apply v
  have hG : functorVertex G = w := (functorVertexEquiv _ C).apply_symm_apply w
  have ei : FunctorIso F G := by
    change VertexIso (functorVertex F) (functorVertex G)
    rw [hF, hG]
    exact e
  constructor
  · have ez := VertexIso.map ei (evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    rw [evaluateFunctorAt_functorVertex, evaluateFunctorAt_functorVertex] at ez
    exact hv.1.of_vertexIso ez
  · exact IsPushoutSquare.of_functorIso hv.2 ei

/-- 概要：cofiber 図式の span の元の C 内での点ごとの押し出しは全頂点で cofiber。
方針：cofiber 図式内の押し出しと包含後の同型を各パラメーターで評価する。
規約：C 内での同じ正規化した選択を保つ。使われ方：raw ρ の cofiber 性。 -/
lemma pointwiseCofiberPushout_vertex {K C : SSet.{u}} [Quasicategory C] [IsStable C]
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ cofiberDiagrams C) (k : K _⦋0⦌) :
    IsCofiberDiagramVertex
      ((pointwiseDiagramPushoutApex
        (F ≫ (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι)).app (Opposite.op ⦋0⦌) k) := by
  let G := pointwisePushoutApex (curry F)
  let e := pointwiseDiagramPushoutApex_postcompIso F
    (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι
      (cofiberInclusion_preservesSConstructionData C)
  have ek := VertexIso.map e (evaluateFunctorAt k)
  rw [evaluateFunctorAt_functorVertex, evaluateFunctorAt_functorVertex] at ek
  exact (fullSubcomplexOnVertices_vertex (G.app (Opposite.op ⦋0⦌) k)).of_vertexIso ek

/-- 概要：C 内での点ごとの押し出しの apex を全 cofiber 図式へ持ち上げる。
方針：全頂点の cofiber 性で全部分複体に持ち上げる。
規約：元の正方形を変更しない。使われ方：McCarthy の ρ の cofiber 値の族。 -/
def pointwiseCofiberPushout {K C : SSet.{u}} [Quasicategory C] [IsStable C]
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ cofiberDiagrams C) : K ⟶ cofiberDiagrams C :=
  fullSubcomplexLift _
    (pointwiseDiagramPushoutApex (F ≫ (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι))
      (pointwiseCofiberPushout_vertex F)

/-- 概要：cofiber 値への持ち上げは元の C 内の正方形を厳密に回収する。
方針：全部分複体の包含との合成。
規約：全単体での等号。使われ方：raw ρ の自然性と正規化の回収。 -/
lemma pointwiseCofiberPushout_ι {K C : SSet.{u}} [Quasicategory C] [IsStable C]
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ cofiberDiagrams C) :
    pointwiseCofiberPushout F ≫ (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
      pointwiseDiagramPushoutApex (F ≫ (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) := rfl

end SerrePositivity.KST.SConstruction
