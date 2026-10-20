module
public import SerrePositivity.KST.SConstruction.PerfectDGStableModel
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionPerfect

/-! # 厳密 dg 関手の実射影的 Perf への延長
概要：graph 延長を全次数 Hom を保持して射影的 perfect dg 加群へ制限する。
方針：射影性の保存と、射影解像度による導来延長の実計算を使う。
規約：H⁰ の比較関手を dg 関手と扱わない。使われ方：K-4d の dg 関手性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 実 graph 延長は射影的 perfect 加群を射影的 perfect 加群へ送る。 -/
lemma dgModuleExtension_perfectProjective {M : RightModule A D}
    (hM : modulePerfectProjectiveOver A D Set.univ M) :
    modulePerfectProjectiveOver A E Set.univ ((dgModuleExtension A D E F).obj M) := by
  refine ⟨dgModuleExtension_homotopicallyProjective A D E F hM.1, ?_⟩
  let R := moduleIdentityProjectiveResolution A D (ForgetEnrichment.of (Complex A) M) hM.1
  exact (modulePerfect A E).prop_of_iso
    (dgDerivedExtensionResolutionComputation A D E F R)
    (dgDerivedExtension_perfect A D E F hM.2)

/-- 任意の厳密 dg 関手による、全 Hom 複体を保つ実 Perf dg 関手。 -/
def perfectDGExtension : DGFunctor A (PerfectDGModule A D) (PerfectDGModule A E) :=
  (dgModuleExtension A D E F).restrict (modulePerfectProjectiveOver A D Set.univ)
    (modulePerfectProjectiveOver A E Set.univ)
    (fun _ hM => dgModuleExtension_perfectProjective A D E F hM)

/-- 全 dg 加群への包含後は、元の graph 延長そのものを回収する。 -/
lemma perfectDGExtension_inclusion :
    (perfectDGExtension A D E F).comp (perfectDGModuleInclusion A E Set.univ) =
      (perfectDGModuleInclusion A D Set.univ).comp (dgModuleExtension A D E F) :=
  DGFunctor.restrict_comp_inclusion _ _ _ _

end SerrePositivity.KST.SConstruction
