module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeAugmentationIdentity
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.HomologyCoconeCriterion
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.UniversalCoconeHomology
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ProjectiveBarNativeCocone
/-!
概要：正規化 bar の同じ native 余錐の評価ホモロジーは filtered 余極限である。
方針：実増大の恒等性で C1 の余核を、元の全脚を持つホモロジー余錐へ移す。
規約：入力の coherent 高次成分と元の native 余錐を保持する。
使われ方：c2 の評価空間への接続で使う、全整数次数の余錐比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

def dgBarCompactNativeHomologyCocone_isColimit (x : D) (q : ℤ) :
    IsColimit (dgCoherentCoconeHomology R D G
      (dgCoherentBarNormalizedNativeCoconeUnconditional R D G) x q) := by
  let c := dgCoherentBarNormalizedNativeCoconeUnconditional R D G
  let f := dgCoherentBarCoconeUniversalMap R D G
    (dgCoherentBarMaurerCartan_unconditional R D G) c
  letI : IsIso f := dgBarCompactNativeAugmentation_isIso R D G _
  apply dgBarCompactHomologyCocone_isColimit_of_cokernel
  have aux (p q : ℤ) (hpq : p + 1 = q) :
      IsColimit (CokernelCofork.ofπ
        (dgHomologyBarNondegAugmentation R _ (dgCoherentCoconeHomology R D G c x q))
        (dgHomologyBarNondegAugmentation_d_one R _ _)) := by
    subst q
    let e := asIso (HomologicalComplex.homologyMap ((moduleEvaluation R D x).map f) (p + 1))
    exact IsColimit.ofIsoColimit (dgCoherentBarHomologyBarIsCokernel R D G x p)
      (Cofork.ext e (dgBarCoconeUniversal_homology R D G c x (p + 1)))
  exact aux (q - 1) q (by omega)

lemma dgBarCompactProjectiveBarCocone_ambient
    {I : SSet.{u}}
    (H : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgProjectiveModuleNerve R D) :
    fullInclusionCocone R (RightModule R D) (dgModuleProjectiveProperty R D)
      (dgProjectiveBarNativeCocone R D H) =
      dgCoherentBarNormalizedNativeCoconeUnconditional R D (dgProjectiveBarDiagram R D H) := by
  apply Subtype.ext
  exact fullInclusionLift_comp R (RightModule R D) (dgModuleProjectiveProperty R D) _
    (dgProjectiveBarNativeCocone_vertices R D H)

def dgBarCompactProjectiveHomologyCocone_isColimit
    (H : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶ dgProjectiveModuleNerve R D)
    (x : D) (q : ℤ) :
    IsColimit (dgCoherentCoconeHomology R D (dgProjectiveBarDiagram R D H)
      (fullInclusionCocone R (RightModule R D) (dgModuleProjectiveProperty R D)
        (dgProjectiveBarNativeCocone R D H)) x q) := by
  rw [dgBarCompactProjectiveBarCocone_ambient]
  exact dgBarCompactNativeHomologyCocone_isColimit R D _ x q

end SerrePositivity.InfinityCategories
