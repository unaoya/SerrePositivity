module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeJoinRightNativeRestriction
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationCocone
public import SerrePositivity.InfinityCategories.Stable.InitialTransport

/-!
概要：一つの大域図式の両端の native 余錐同値に沿って保存性を移す。
方針：左余錐を全体へ同型まで持ち上げ、その同じ像を右端へ制限する。
規約：指定する右余錐との比較は頂点だけでなく全余錐の同型。
使われ方：共同分類族に対する Kan 合成と κ-filtered 余極限の保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 両端の native 全余錐制限が同値なら、左の保存性を指定右余錐へ移せる。 -/
lemma mapJoinCocone_isColimit_of_nativeRestrictions
    {A B K X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (H : K ⟶ X) (i : A ⟶ K) (r : B ⟶ K) (G : X ⟶ Y)
    (hi : IsQCatEquivalence (sliceUnderRestrict H i))
    (hiG : IsQCatEquivalence (sliceUnderRestrict (H ≫ G) i))
    (hr : IsQCatEquivalence (sliceUnderRestrict H r))
    (hrG : IsQCatEquivalence (sliceUnderRestrict (H ≫ G) r))
    (d : JoinCocone (i ≫ H)) (hd : IsColimitCone d)
    (hGd : IsColimitCone (mapJoinCocone G d))
    (c : JoinCocone (r ≫ H)) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone G c) := by
  obtain ⟨a₀, ⟨e₀⟩⟩ := hi.choose.isEssentiallySurjective d
  let a : JoinCocone H := a₀
  have e : VertexIso (X := sliceUnder (i ≫ H)) (a.restrict i) d := e₀
  have hai : IsColimitCone (a.restrict i) := hd.of_vertexIso e.symm
  have ha : IsColimitCone a := (hi.choose.isInitialVertex_iff a).mpr hai
  have hGai : IsColimitCone (mapJoinCocone G (a.restrict i)) :=
    hGd.of_vertexIso (e.map (sliceUnderPostcomp (i ≫ H) G)).symm
  have hGa : IsColimitCone (mapJoinCocone G a) :=
    (hiG.choose.isInitialVertex_iff (mapJoinCocone G a)).mpr hGai
  have har : IsColimitCone (a.restrict r) := (hr.choose.isInitialVertex_iff a).mp ha
  have hGar : IsColimitCone (mapJoinCocone G (a.restrict r)) :=
    (hrG.choose.isInitialVertex_iff (mapJoinCocone G a)).mp hGa
  let er : VertexIso (X := sliceUnder (r ≫ H)) (a.restrict r) c :=
    colimitConeIso (a.restrict r) c har hc
  exact hGar.of_vertexIso (er.map (sliceUnderPostcomp (r ≫ H) G))

end SerrePositivity.InfinityCategories.F2.Ind
