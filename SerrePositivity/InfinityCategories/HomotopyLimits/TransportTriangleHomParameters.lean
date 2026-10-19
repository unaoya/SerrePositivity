module

public import SerrePositivity.InfinityCategories.HomotopyLimits.TransportTriangleInitialHom

/-!
概要：輸送三角形の全 Hom の始域を、元の指定終点 c の Hom に厳密に揃える。
方針：終点の底の等式でパラメータを移し、同じ円柱をその射で前合成する。
規約：Hom パラメータも評価固定の中間円柱も選び直さない。
使われ方：左右の輸送三角形を同じ span 頂点からの全 Hom で比較する。
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

/-- 元の指定終点からの Hom を、同じ実際の輸送終点の Hom パラメータへ移す厳密な同型。 -/
def transportTriangleHomParameterIso :
    pinchedHomLeft c y ≅ pinchedHomLeft (p.app (Opposite.op ⦋0⦌) dᵀ) y :=
  eqToIso (congrArg (fun z ↦ pinchedHomLeft z y)
    (transportTriangleTerminalVertex_projection p (e := e) (f := f) v).symm)

/-- 同じ元の指定終点の Hom 上で表示した、実際の輸送終点の全 Hom の族。 -/
def transportTrianglePointHomNormalized : pinchedHomLeft c y ⟶ vertexFiber p y :=
  (transportTriangleHomParameterIso p (e := e) (f := f) v y).hom ≫
    leftFibrationPointHomFamily p dᵀ y

/-- 同じパラメータで表示した、元の実際の三角形全体の族。 -/
def transportTriangleHomNormalized :
    pinchedHomLeft c y ⟶ sliceUnder (coherentTransportTriangleVertex p σ v) :=
  (transportTriangleHomParameterIso p (e := e) (f := f) v y).hom ≫
    transportTriangleHomFamily p σ v y

/-- 正規化しても、可変終点は同じ全 Hom の族そのもの。 -/
lemma transportTriangleHomNormalized_endpoint :
    transportTriangleHomNormalized p σ v y ≫
      sliceUnderProjection (coherentTransportTriangleVertex p σ v) =
        transportTrianglePointHomNormalized p (e := e) (f := f) v y ≫ vertexFiberι p y := by
  rw [transportTriangleHomNormalized, Category.assoc, transportTriangleHomFamily_endpoint]
  rfl

/-- 同じパラメータ上での、元の始点を保つ中間 Hom の族。 -/
def transportTriangleInitialHomNormalized :
    pinchedHomLeft c y ⟶ leftFibrationInitialTotal p v.val y :=
  (transportTriangleHomParameterIso p (e := e) (f := f) v y).hom ≫
    transportTriangleInitialHomFamily p σ v y

/-- 同じパラメータ上でも、中間 Hom の評価は元の全 Hom の族を厳密に回収する。 -/
lemma transportTriangleInitialHomNormalized_evaluation :
    transportTriangleInitialHomNormalized p σ v y ≫ leftFibrationInitialEvaluation p v.val y =
      transportTrianglePointHomNormalized p (e := e) (f := f) v y := by
  rw [transportTriangleInitialHomNormalized, Category.assoc,
    transportTriangleInitialHomFamily_evaluation]
  rfl

variable (hv : IsInitialVertex v.val)

/-- 評価固定の同じ中間円柱を、指定終点の全 Hom 上で厳密に前合成する。 -/
def transportTriangleInitialHomNormalizedComparison : SSet.Homotopy
    (transportTrianglePointHomNormalized p (e := e) (f := f) v y ≫
      leftFibrationInitialSection p v.val hv y)
    (transportTriangleInitialHomNormalized p σ v y) := by
  let H := functorHomotopyPrecomp (transportTriangleInitialHomComparison p σ v y hv).homotopy
    (transportTriangleHomParameterIso p (e := e) (f := f) v y).hom
  exact
    { h := H.h
      h₀ := by
        change SSet.ι₀ ≫ H.h = transportTrianglePointHomNormalized p (e := e) (f := f) v y ≫
          leftFibrationInitialSection p v.val hv y
        simpa only [transportTrianglePointHomNormalized, Category.assoc] using H.h₀
      h₁ := by
        change SSet.ι₁ ≫ H.h = transportTriangleInitialHomNormalized p σ v y
        exact H.h₁
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }

/-- 前合成した同じ円柱も、元の全 Hom の族の評価を全時刻で固定する。 -/
lemma transportTriangleInitialHomNormalizedComparison_evaluation :
    (transportTriangleInitialHomNormalizedComparison p σ v y hv).h ≫
      leftFibrationInitialEvaluation p v.val y =
        fst (pinchedHomLeft c y) Δ[1] ≫
          transportTrianglePointHomNormalized p (e := e) (f := f) v y := by
  dsimp only [transportTriangleInitialHomNormalizedComparison, functorHomotopyPrecomp]
  rw [Category.assoc, (transportTriangleInitialHomComparison p σ v y hv).evaluation,
    ← Category.assoc, whiskerRight_fst, Category.assoc]
  rfl

/-- 指定終点の Hom 上での、同じ実際の三角形を通した元の Hom 比較の円柱。 -/
def transportTriangleInitialHomNormalizedHomotopy : SSet.Homotopy
    (transportTrianglePointHomNormalized p (e := e) (f := f) v y ≫
      leftFibrationInitialHomComparison p v.val hv y)
    (transportTriangleInitialHomNormalized p σ v y ≫ leftFibrationInitialProjection p v.val y ≫
      (leftFibrationInitialBaseIso p v.val y).hom) := by
  let H := functorHomotopyPostcomp (transportTriangleInitialHomNormalizedComparison p σ v y hv)
    (leftFibrationInitialProjection p v.val y ≫ (leftFibrationInitialBaseIso p v.val y).hom)
  exact
    { h := H.h
      h₀ := by
        change SSet.ι₀ ≫ H.h = transportTrianglePointHomNormalized p (e := e) (f := f) v y ≫
          leftFibrationInitialHomComparison p v.val hv y
        simpa only [Category.assoc, leftFibrationInitialHomComparison] using H.h₀
      h₁ := by
        change SSet.ι₁ ≫ H.h = transportTriangleInitialHomNormalized p σ v y ≫
          leftFibrationInitialProjection p v.val y ≫ (leftFibrationInitialBaseIso p v.val y).hom
        exact H.h₁
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }

/-- 正規化した Hom 比較の円柱も、同じ評価固定の中間円柱の像そのもの。 -/
lemma transportTriangleInitialHomNormalizedHomotopy_projection :
    (transportTriangleInitialHomNormalizedHomotopy p σ v y hv).h =
      (transportTriangleInitialHomNormalizedComparison p σ v y hv).h ≫
        leftFibrationInitialProjection p v.val y ≫ (leftFibrationInitialBaseIso p v.val y).hom :=
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
