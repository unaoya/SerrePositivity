module
public import SerrePositivity.InfinityCategories.Derived.ResolutionOutputComparisonComposition
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionPrecompComposition
public import SerrePositivity.InfinityCategories.Derived.DGUniverseLiftInputComposition
/-!
概要：元の指定出力分解の全関手比較は、二段の dg 入力前合成を保つ。
方針：同じ実 dg 分解関手と宇宙持ち上げの合成等式を、指定出力比較の合成則へ渡す。
規約：既存の比較定義と指定切断を保持する。使われ方：一般 kernel の合成子照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (A B C : Type v)
  [DGCategory R A] [DGCategory R B] [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
/-- 二段前合成の元の指定出力比較は、合成 dg 入力の同じ比較に型付きで一致する。 -/
lemma dgModuleOutputResolution_precompIso_comp_heq
    (H : DGFunctor R A B) (J : DGFunctor R B C) (F : DGFunctor R C (RightModule R E)) :
    HEq (dgModuleOutputResolution_precompIso R A C E (H.comp J) F)
      (dgModuleOutputResolution_precompIso R A B E H (J.comp F) ≪≫
        (dgModuleOutputResolution_precompIso R B C E J F).precomp
          (dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
            (H.comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R B))))) := by
  let Q := dgModuleFunctorResolutionSourceNerveEquivalence R A E ((H.comp J).comp F)
  let S := dgModuleFunctorResolutionSourceNerveEquivalence R B E (J.comp F)
  let T := dgModuleFunctorResolutionSourceNerveEquivalence R C E F
  let h := dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
    (H.comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R B)))
  let k := dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) w} R B).comp
    (J.comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R C)))
  let PH := dgNerve.map (dgModuleResolutionPrecompFunctor R A B E H (J.comp F))
  let PJ := dgNerve.map (dgModuleResolutionPrecompFunctor R B C E J F)
  let RX := dgNerve.map (dgModuleFunctorResolutionReplacementLift R A E ((H.comp J).comp F))
  let RY := dgNerve.map (dgModuleFunctorResolutionReplacementLift R B E (J.comp F))
  let RZ := dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E F)
  have hs : PH ≫ S.hom = Q.hom ≫ h := by
    have e := congrArg (fun G => dgNerve.map G)
      (dgModuleResolutionPrecompFunctor_sourceLift R A B E H (J.comp F))
    simpa only [dgNerve.map_comp] using! e
  have ht : PJ ≫ T.hom = S.hom ≫ k := by
    have e := congrArg (fun G => dgNerve.map G)
      (dgModuleResolutionPrecompFunctor_sourceLift R B C E J F)
    simpa only [dgNerve.map_comp] using! e
  have hr : PH ≫ RY = RX := by
    have e := congrArg (fun G => dgNerve.map G)
      (dgModuleResolutionPrecompFunctor_replacementLift R A B E H (J.comp F))
    simpa only [dgNerve.map_comp] using! e
  have hj : PJ ≫ RZ = RY := by
    have e := congrArg (fun G => dgNerve.map G)
      (dgModuleResolutionPrecompFunctor_replacementLift R B C E J F)
    simpa only [dgNerve.map_comp] using! e
  have hu : (PH ≫ PJ) ≫ T.hom = Q.hom ≫ (h ≫ k) := by
    rw [Category.assoc, ht, ← Category.assoc, hs, Category.assoc]
  have huR : (PH ≫ PJ) ≫ RZ = RX := by rw [Category.assoc, hj, hr]
  let P0 := dgNerve.map (dgModuleResolutionPrecompFunctor R A C E (H.comp J) F)
  let h0 := dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
    ((H.comp J).comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R C)))
  have hb : h ≫ k = h0 := by
    dsimp only [h, k, h0]
    rw [← dgNerve.map_comp, dgUniverseLift_inputPrecomp_comp]
  have hg : PH ≫ PJ = P0 := by
    have e := congrArg (fun G => dgNerve.map G)
      (dgModuleResolutionPrecompFunctor_comp R A B C E H J F)
    simpa only [dgNerve.map_comp] using! e.symm
  have hs0 : P0 ≫ T.hom = Q.hom ≫ h0 := by rw [← hg, hu, hb]
  have hr0 : P0 ≫ RZ = RX := by rw [← hg, huR]
  have hc := qCatResolutionOutputPrecompIso_comp Q S T h k PH PJ RX RY RZ
    hs ht hu hr hj huR
  have hl := qCatResolutionOutputPrecompIso_heq_of_maps Q T RX RZ hb.symm hg.symm
    hs0 hr0 hu huR
  simpa only [dgModuleOutputResolution_precompIso, Q, S, T, h, k, PH, PJ, RX, RY, RZ,
    P0, h0] using! hl.trans (heq_of_eq hc)
end SerrePositivity.InfinityCategories
