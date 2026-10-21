module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecomposition
/-!
概要：実出力分解の同じ切断を、元の対象宇宙の入力射影へ接続する。
方針：持ち上げた射影の厳密切断と対象宇宙の上げ下げの相殺を使う。
規約：全単体上の厳密等式。使われ方：通常の h における主導来作用の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
/-- 同じ実切断を元の入力射影へ合成すると、全単体上で恒等になる。 -/
lemma dgModuleResolvedSourceSection_comp_source
    (F : DGFunctor R C (RightModule R E)) :
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
      (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv) ≫
        dgNerve.map (dgModuleFunctorResolutionSource R C E F) = 𝟙 _ := by
  have hs : (dgModuleFunctorResolutionSourceLift R C E F).comp
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C) =
        dgModuleFunctorResolutionSource R C E F := by
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro x y
    simp only [dgModuleFunctorResolutionSourceLift, EnrichedFunctor.comp_map,
      dgUniverseLiftUp, dgUniverseLiftDown, dgObjectImageEvaluation,
      Category.comp_id, eqToHom_refl]
  rw [← hs, dgNerve.map_comp]
  simp only [← Category.assoc]
  rw [Category.assoc (dgNerve.map _) _ (dgNerve.map _),
    dgModuleFunctorResolutionSourceNerveEquivalence_inv_hom, Category.comp_id,
    ← dgNerve.map_comp, dgUniverseLiftUp_comp_down, dgNerve.map_id]
end SerrePositivity.InfinityCategories
