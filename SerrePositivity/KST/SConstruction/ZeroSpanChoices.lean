module
public import SerrePositivity.KST.SConstruction.ZeroSpanData
public import SerrePositivity.KST.SConstruction.ColimitBaseTransport
public import SerrePositivity.InfinityCategories.Stable.Definition

/-! # 固定した第一辺の零脚の比較
概要：同じ第一辺を持ち、第二辺が零対象に向かう二つの span は coherent に同型である。
方針：零脚のデータの trivial Kan fibration の同じ fiber 内で比較する。
規約：零頂点と零射を厳密に保持してデータへ含める。
使われ方：BGT Lemma 7.3、指定した零脚の span の余極限の存在。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：第一辺の等しい零脚つき span の族は coherent に同型。
方針：零脚のデータに持ち上げ、trivial Kan fibration の同じ持ち上げ同士を比較する。
規約：C は零対象を持つだけでよい。使われ方：パラメーター付き零脚の選択の変更。 -/
def zeroSpanFamiliesIso {A C : SSet.{u}} [HasZeroVertex C]
    (p q : A ⟶ (ihom (horn 2 0 : SSet.{u})).obj C)
    (hp : ∀ v : A _⦋0⦌, IsZeroTargetArrow
      (((pre horn₂₀.ι₀₂).app C).app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) v)))
    (hq : ∀ v : A _⦋0⦌, IsZeroTargetArrow
      (((pre horn₂₀.ι₀₂).app C).app (Opposite.op ⦋0⦌) (q.app (Opposite.op ⦋0⦌) v)))
    (h : p ≫ (pre horn₂₀.ι₀₁).app C = q ≫ (pre horn₂₀.ι₀₁).app C) : FunctorIso p q := by
  have he : zeroSpanDataLift p hp ≫ zeroSpanDataProjection C =
      zeroSpanDataLift q hq ≫ zeroSpanDataProjection C := by
    rw [zeroSpanDataLift_projection, zeroSpanDataLift_projection, h]
  have e := (functorIsoOfTrivialKanFibration (zeroSpanDataProjection C)
    (zeroSpanDataLift p hp) (zeroSpanDataLift q hq) he).postcomp (zeroSpanDataDiagram C)
  simpa only [zeroSpanDataLift_diagram] using e

/-- 概要：同じ第一辺を持つ二つの零脚つき span の図式は関手として同型。
方針：一点パラメーターの族として比較し、その点で評価する。
規約：同型は全 span の coherent な同型。使われ方：余極限の存在を任意の零脚に移す。 -/
def zeroSpanDiagramsIso {C : SSet.{u}} [HasZeroVertex C]
    (p q : (horn 2 0 : SSet.{u}) ⟶ C)
    (hp : IsZeroTargetArrow (functorVertex (horn₂₀.ι₀₂ ≫ p)))
    (hq : IsZeroTargetArrow (functorVertex (horn₂₀.ι₀₂ ≫ q)))
    (h : horn₂₀.ι₀₁ ≫ p = horn₂₀.ι₀₁ ≫ q) : FunctorIso p q := by
  let P : (Δ[0] : SSet.{u}) ⟶ (ihom (horn 2 0 : SSet.{u})).obj C := SSet.const (functorVertex p)
  let Q : (Δ[0] : SSet.{u}) ⟶ (ihom (horn 2 0 : SSet.{u})).obj C := SSet.const (functorVertex q)
  have hP (v : (Δ[0] : SSet.{u}) _⦋0⦌) : IsZeroTargetArrow
      (((pre horn₂₀.ι₀₂).app C).app (Opposite.op ⦋0⦌) (P.app (Opposite.op ⦋0⦌) v)) := by
    change IsZeroTargetArrow (((pre horn₂₀.ι₀₂).app C).app (Opposite.op ⦋0⦌)
      (PinchedHom.constant (functorVertex p) 0))
    rw [pinchedConstant_zero]
    exact hp
  have hQ (v : (Δ[0] : SSet.{u}) _⦋0⦌) : IsZeroTargetArrow
      (((pre horn₂₀.ι₀₂).app C).app (Opposite.op ⦋0⦌) (Q.app (Opposite.op ⦋0⦌) v)) := by
    change IsZeroTargetArrow (((pre horn₂₀.ι₀₂).app C).app (Opposite.op ⦋0⦌)
      (PinchedHom.constant (functorVertex q) 0))
    rw [pinchedConstant_zero]
    exact hq
  have hPQ : P ≫ (pre horn₂₀.ι₀₁).app C = Q ≫ (pre horn₂₀.ι₀₁).app C := by
    rw [SSet.const_comp, SSet.const_comp]
    change SSet.const (functorVertex (horn₂₀.ι₀₁ ≫ p)) =
      SSet.const (functorVertex (horn₂₀.ι₀₁ ≫ q))
    rw [h]
  let e := zeroSpanFamiliesIso P Q hP hQ hPQ
  have he := VertexIso.map e (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
  change VertexIso (PinchedHom.constant (functorVertex p) 0)
    (PinchedHom.constant (functorVertex q) 0) at he
  simpa only [pinchedConstant_zero] using he

/-- 概要：安定な quasicategory では零対象へ向かう脚を持つ任意の span が余極限を持つ。
方針：同じ第一辺の選んだ cofiber の span と関手同型で比較し、余極限の存在を移す。
規約：指定された零頂点と零射を変えない。使われ方：高次数の相対 cofiber 補完。 -/
lemma hasColimit_zeroSpan {C : SSet.{u}} [Quasicategory C] [IsStable C]
    (p : (horn 2 0 : SSet.{u}) ⟶ C)
    (hp : IsZeroTargetArrow (functorVertex (horn₂₀.ι₀₂ ≫ p))) : HasColimit p := by
  let f := horn₂₀.ι₀₁ ≫ p
  let t := chosenCofiberSquare (edgeOfSimplex (SSet.yonedaEquiv f))
  have ht : squareBottomEdge ≫ t.square = f := by
    rw [t.bottom_edge]
    exact SSet.yonedaEquiv.symm_apply_apply f
  let q := pushoutSpan t.square
  have hq : IsZeroTargetArrow (functorVertex (horn₂₀.ι₀₂ ≫ q)) := by
    change IsZeroVertex ((evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
      (Opposite.op ⦋0⦌) (functorVertex (horn₂₀.ι₀₂ ≫ q)))
    rw [evaluateFunctorAt_functorVertex]
    change IsZeroVertex ((horn₂₀.ι₀₂ ≫ spanSquareBoundary ≫ t.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    rw [← Category.assoc, spanSquareBoundary_leftEdge]
    exact t.zero_corner
  have he : horn₂₀.ι₀₁ ≫ p = horn₂₀.ι₀₁ ≫ q := by
    change f = horn₂₀.ι₀₁ ≫ spanSquareBoundary ≫ t.square
    rw [← Category.assoc, spanSquareBoundary_bottomEdge, ht]
  exact HasColimit.of_functorIso ⟨pushoutCocone t.square, t.isPushout⟩
    (zeroSpanDiagramsIso p q hp hq he)

end SerrePositivity.KST.SConstruction
