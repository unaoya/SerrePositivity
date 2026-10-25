module
public import SerrePositivity.InfinityCategories.Derived.DGStandardClosedPostcomposition
public import SerrePositivity.InfinityCategories.Derived.DGStandardHomChainMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.ClosedPrecompositionComponents
/-!
概要：標準 DK の豊穣前合成を、同じ全 Hom 鎖写像の全単体作用へ同定する。
方針：閉定数の AW 成分式と豊穣前合成の次数別式を照合する。
規約：対象圏の Small 性を仮定しない。
使われ方：D-8 c5 の余積包含による実 Hom の積の検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DoldKanComparison DGNerve.PinchedHom SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]

lemma dgStandardClosedConstant_eq {x y : D}
    (f : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y) (n : ℕ) :
    (standardHomSpace (R := R) x y).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (closedStandardVertexEquiv (R := R) (D := D) x y f) =
        standardConstant (closedHomEquiv R D x y f) n := by
  have h := dgStandardSimplicialPostcomp_app R D x x y f n (standardUnit x n)
  change standardAW ((standardHomSpace (R := R) x y).map
    (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (closedStandardVertexEquiv (R := R) (D := D) x y f)) (standardUnit x n) = _ at h
  simpa only [standardAW_unit_right] using h

lemma dgStandardSimplicialPrecomp_chainMap {x y z : D}
    (f : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y) :
    eHomWhiskerRight SSet f (ForgetEnrichment.of (Complex R) z) =
      dgStandardHomChainMap
        (eHomWhiskerRight (Complex R) f (ForgetEnrichment.of (Complex R) z)) := by
  ext n s
  change standardAW s ((standardHomSpace (R := R) x y).map
    (SimplexCategory.const ⦋n.unop.len⦌ ⦋0⦌ 0).op
      (closedStandardVertexEquiv (R := R) (D := D) x y f)) = _
  rw [dgStandardClosedConstant_eq]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨L, k⟩, hL, hk⟩
  change (awData s.val (standardConstant (closedHomEquiv R D x y f) _).val).component
    L k hL hk = (dgStandardSimplexMap _ s).val.component L k hL hk
  rw [awData_closed_pre_component, dgStandardSimplexMap_component]
  exact (dgGluingHomWhiskerRight_f R D (x := x) (y := y) (z := z) f k
    (s.val.component L k hL hk)).symm

end SerrePositivity.InfinityCategories
