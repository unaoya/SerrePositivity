module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechAcyclic
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechSplitIntersection

/-!
概要：指定開集合との交叉が同じ被覆を、同じ係数の Čech 計算で比較する。
方針：各有限交叉の等式を、前層の値の自然同型に移す。
規約：被覆の開集合自体の等式は仮定せず、指定開集合内での等式だけを使う。
使われ方：標準開の切断を、更に小さいアフィン交叉へ制限する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v} [CommRing R]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) {ι : Type} [LinearOrder ι]
variable (W : Opens X) (U V : ι → Opens X)

/-- 指定開集合との各交叉の等式を、有限交叉の等式へ移す。 -/
theorem cechOpenRestrictedIntersection_eq (h : ∀ i, W ⊓ U i = W ⊓ V i) (T : Finset ι) :
    W ⊓ cechOpenIntersection U T = W ⊓ cechOpenIntersection V T := by
  induction T using Finset.induction_on with
  | empty => simp [cechOpenIntersection]
  | @insert i T hi ih =>
    rw [cechOpenIntersection_insert, cechOpenIntersection_insert, ← inf_assoc, h i]
    calc
      (W ⊓ V i) ⊓ cechOpenIntersection U T = V i ⊓ (W ⊓ cechOpenIntersection U T) := by
        rw [inf_comm W (V i), inf_assoc]
      _ = V i ⊓ (W ⊓ cechOpenIntersection V T) := congrArg (fun Z ↦ V i ⊓ Z) ih
      _ = W ⊓ (V i ⊓ cechOpenIntersection V T) := by
        rw [← inf_assoc, inf_comm (V i) W, inf_assoc]

/-- 指定開集合内で同じ被覆の、有限交叉の係数図式の自然同型。 -/
def openCoverCechRestrictedCoverIso (h : ∀ i, W ⊓ U i = W ⊓ V i) :
    openCoverCechDiagram (openCoverIntersectionPresheaf P W) U ≅
      openCoverCechDiagram (openCoverIntersectionPresheaf P W) V :=
  NatIso.ofComponents (fun T ↦ P.mapIso (eqToIso
    (congrArg op (cechOpenRestrictedIntersection_eq W U V h T)))) (by
      intro T S hTS
      change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
      rw [← P.map_comp, ← P.map_comp]
      congr 1)

/-- 指定開集合内で同じ被覆へ、増大 Čech の完全性を移す。 -/
theorem openCoverCechAcyclic_of_intersection_eq (h : ∀ i, W ⊓ U i = W ⊓ V i)
    (hU : OpenCoverCechAcyclic (openCoverIntersectionPresheaf P W) U) :
    OpenCoverCechAcyclic (openCoverIntersectionPresheaf P W) V where
  injective_zero := fullCechCoefficientEquiv_zero_injective
    (openCoverCechRestrictedCoverIso P W U V h) hU.injective_zero
  exact k := fullCechCoefficientEquiv_exact (openCoverCechRestrictedCoverIso P W U V h)
    k (hU.exact k)

/-- 二段階の交叉前層は、交叉した開集合の前層に自然に同型。 -/
def openCoverIntersectionPresheafNestedIso (Z : Opens X) :
    openCoverIntersectionPresheaf (openCoverIntersectionPresheaf P W) Z ≅
      openCoverIntersectionPresheaf P (W ⊓ Z) :=
  NatIso.ofComponents (fun O ↦ P.mapIso (eqToIso
    (congrArg op (inf_assoc W Z O.unop).symm))) (by
      intro O O' h
      change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
      rw [← P.map_comp, ← P.map_comp]
      congr 1)

/-- 小さい開集合での交叉なら、先の大きい開集合の制限は冗長になる。 -/
def openCoverIntersectionPresheafNestedIsoOfLe (Z : Opens X) (h : Z ≤ W) :
    openCoverIntersectionPresheaf (openCoverIntersectionPresheaf P W) Z ≅
      openCoverIntersectionPresheaf P Z :=
  openCoverIntersectionPresheafNestedIso P W Z ≪≫
    eqToIso (congrArg (openCoverIntersectionPresheaf P) (inf_eq_right.mpr h))

end SerrePositivity.AlgebraicGeometry
