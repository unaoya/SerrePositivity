module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.LinearHomCohomology
public import SerrePositivity.InfinityCategories.Derived.DGStandardClosedPrecomposition
/-!
概要：標準豊穣後合成を元の閉射の全 Hom 鎖写像へ同定する。
方針：閉定数との AW 合成を各斉次成分で照合する。
規約：全単体で厳密に一致し、小ささの仮定を追加しない。
使われ方：coslice の線形係数作用をコホモロジーチャートの自然性へ渡す。
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

lemma dgBarCompactStandardSimplicialPostcomp_chainMap {x y z : D}
    (f : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z) :
    eHomWhiskerLeft SSet (ForgetEnrichment.of (Complex R) x) f =
      moduleUnderlyingSSetMap (dgBarCompactStandardModuleMap
        (dgClosedPostcomposition R D (x := x) f)) := by
  ext n s
  change standardAW ((standardHomSpace (R := R) y z).map
    (SimplexCategory.const ⦋n.unop.len⦌ ⦋0⦌ 0).op
      (closedStandardVertexEquiv (R := R) (D := D) y z f)) s = _
  rw [dgStandardClosedConstant_eq]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (awData (standardConstant (closedHomEquiv R D y z f) _).val s.val).component
    J k hJ hk = (dgStandardSimplexMap _ s).val.component J k hJ hk
  rw [awData_closed_post_component, dgStandardSimplexMap_component]
  exact (dgClosedPostcomposition_f R D (x := x) f k (s.val.component J k hJ hk)).symm

end SerrePositivity.InfinityCategories
