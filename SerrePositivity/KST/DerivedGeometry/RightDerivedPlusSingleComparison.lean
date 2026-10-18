module

public import SerrePositivity.KST.DerivedGeometry.RightDerivedPlusSingleBounds
public import SerrePositivity.KST.DerivedGeometry.LeftExactLowestQuasiIso

/-!
概要：非輪状な単一対象では bounded below 右導来の比較写像そのものが同型。
方針：増大写像の零次数準同型性と比較の自然性で零次数を計算し、他の次数の消滅を使う。
規約：比較同型の存在を仮定せず、Mathlib の実際の右導来比較を検証する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の導来単位の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  {X : C} (I : InjectiveResolution X)

/--
概要：単一対象での右導来比較は零次数コホモロジーで同型。
方針：injective 分解の増大と比較の自然性を使い、左完全性で零次数を保つ。
規約：正次数非輪状性は不要。
使われ方：TT §3、Toën §3.2 の導来単位の零次数。
-/
lemma rightDerivedPlusUnit_single_homology_zero_isIso (I : InjectiveResolution X) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (F.rightDerivedFunctorPlusUnit.app ((singleComplexPlus (C := C) 0).obj X))) := by
  let f := injectiveResolutionPlusι I
  have : QuasiIsoAt ((F.mapHomologicalComplex (.up ℤ)).map I.ι') 0 :=
    leftExact_map_quasiIsoAt_zero F I.ι'
  have : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f))) := by
    change IsIso ((DerivedCategory.homologyFunctor D 0).map
      (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map I.ι')))
    exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors D 0)
      ((F.mapHomologicalComplex (.up ℤ)).map I.ι')).mpr
        ((quasiIsoAt_iff_isIso_homologyMap _ 0).mp inferInstance)
  have h := congrArg ((DerivedCategory.Plus.homologyFunctor D 0).map)
    (F.rightDerivedFunctorPlusUnit.naturality f)
  dsimp only [Functor.comp_map] at h
  simp only [Functor.map_comp] at h
  have : IsIso (DerivedCategory.Plus.Q.map f) :=
    injectiveResolutionPlusι_Q_isIso I
  have : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (F.rightDerivedFunctorPlusUnit.app ((singleComplexPlus (C := C) 0).obj X)) ≫
      (DerivedCategory.Plus.homologyFunctor D 0).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f))) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.Plus.homologyFunctor D 0).map
      (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)))

/--
概要：通常の正次数右導来が零の単一対象で右導来比較は同型。
方針：零次数の比較と、両側のそれ以外のコホモロジーの消滅で判定する。
規約：左完全性と非輪状性から実際の比較写像を検証する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン単位。
-/
lemma rightDerivedPlusUnit_single_isIso (X : C)
    (h : ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj X)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app ((singleComplexPlus (C := C) 0).obj X)) := by
  let K := (singleComplexPlus (C := C) 0).obj X
  let S := (F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).obj K
  let T := F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)
  have : S.IsGE 0 := by
    apply (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).mp
    change (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj X))).IsGE 0
    infer_instance
  have : S.IsLE 0 := by
    apply (DerivedCategory.Plus.isLE_ι_obj_iff _ 0).mp
    change (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj X))).IsLE 0
    infer_instance
  have : T.IsGE 0 := rightDerivedPlus_single_isGE F X
  have : T.IsLE 0 := rightDerivedPlus_single_isLE F X h
  apply (DerivedCategory.Plus.isIso_iff _).mpr
  intro n
  by_cases hn : n = 0
  · subst n
    exact rightDerivedPlusUnit_single_homology_zero_isIso F (injectiveResolution X)
  · rcases lt_or_gt_of_ne hn with hn | hn
    · exact (DerivedCategory.Plus.isZero_homology_of_isGE S 0 n hn).isIso
        (DerivedCategory.Plus.isZero_homology_of_isGE T 0 n hn) _
    · exact (DerivedCategory.Plus.isZero_homology_of_isLE S 0 n hn).isIso
        (DerivedCategory.Plus.isZero_homology_of_isLE T 0 n hn) _

end SerrePositivity.KST.DerivedGeometry
