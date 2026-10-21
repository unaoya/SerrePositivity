module
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionPrecomp
/-!
概要：共通対象宇宙の元の nerve 上で、入力前合成に沿う同じ実出力分解を比較する。
方針：対象宇宙の上げ下げの厳密等式を、指定逆からの全関手比較へ渡す。
規約：入力の Small 性と元の出力の射影性は不要。使われ方：二入力 Hom の制限比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (A C : Type (max (u + 1) v w)) [DGCategory R A] [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E))
/-- 同じ入力の対象宇宙の上げ下げは、指定前合成を厳密に保つ。 -/
lemma dgUniverseLift_sourcePrecomp :
    (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R A).comp
      ((dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R A).comp
        (H.comp (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C))) =
      H.comp (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R A).comp
      ((dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R A).comp
        (H.comp (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C))))
    (G := H.comp (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C)) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, dgUniverseLiftUp, dgUniverseLiftDown,
    dgObjectImageEvaluation, Category.comp_id, Category.id_comp, eqToHom_refl]
/-- 元の nerve の入力前合成に沿う、同じ実出力分解の全関手同型。 -/
def dgModuleOutputResolution_unliftedPrecompIso :
    FunctorIso
      (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R A) ≫
        dgModuleOutputResolutionInfinity R A E (H.comp F))
      (dgNerve.map H ≫ dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C) ≫
        dgModuleOutputResolutionInfinity R C E F) := by
  have h := congrArg (fun G => dgNerve.map G)
    (dgUniverseLift_sourcePrecomp.{u, v, w} R A C H)
  simp only [dgNerve.map_comp] at h
  have e := (dgModuleOutputResolution_precompIso R A C E H F).precomp
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R A))
  simp only [dgNerve.map_comp] at e
  simpa only [← Category.assoc, h] using! e
end SerrePositivity.InfinityCategories
