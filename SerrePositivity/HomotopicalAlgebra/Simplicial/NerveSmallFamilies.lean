module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameterEvaluation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftTensor

/-! # Read whole moving coherent systems back as original-universe chain families

The indexing category may be large. Each entire finite chain family, including
its full small parameter, lives in the original universe of its values.
-/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveSmallFamilies
variable {D : Type uD} [Category.{vD} D] (K F : D ⥤ SSet.{v})
  (a : NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K) F)

/-- The full small parameter and full chain simplex are retained before applying an action. -/
def family {n : ℕ} (c : ComposableArrows D n) :
    K.obj (c.obj 0) ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
      F.obj (c.obj (Fin.last n)) :=
  UniverseLift.lowerSimplexTensor (uncurry (a.app (ofChain c)))

lemma family_lift {n : ℕ} (c : ComposableArrows D n) :
    UniverseLift.simplexTensorMap.{w} (family K F a c) = uncurry (a.app (ofChain c)) :=
  UniverseLift.simplexTensorMap_lowerSimplexTensor _

lemma family_naturality {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    K.obj (c.obj 0) ◁ SSet.stdSimplex.map θ ≫ family K F a c =
      ((K.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0))))) ▷
        SSet.stdSimplex.obj (SimplexCategory.mk m) ≫
        family K F a ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
      F.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) := by
  let initialMap := c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))
  let tail := c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))
  have h0 : SSet.stdSimplex.map θ ≫ a.app (ofChain c) =
      (a.app (ofChain ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
        (pre (UniverseLift.map.{w} (K.map initialMap))).app
          (UniverseLift.obj.{w} (F.obj (c.obj (θ.toOrderHom (Fin.last m)))))) ≫
      (ihom (UniverseLift.obj.{w} (K.obj (c.obj 0)))).map
        (UniverseLift.map.{w} (F.map tail)) :=
    NerveBiparameter.reindex_compatibility
      (NerveMovingParameter.lifted.{w} K) (NerveMovingParameter.lifted.{w} F) a c θ
  have h := congrArg (fun k : SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk m) ⟶
    (ihom (UniverseLift.obj.{w} (K.obj (c.obj 0)))).obj
      (UniverseLift.obj.{w} (F.obj (c.obj (Fin.last n)))) => uncurry k) h0
  rw [uncurry_natural_left, uncurry_natural_right, uncurry_pre_app] at h
  apply (show Function.Injective (UniverseLift.simplexTensorMap.{w}
    (K := K.obj (c.obj 0)) (P := F.obj (c.obj (Fin.last n))) (n := m)) from
    by
      intro f g hfg
      have he := congrArg (fun z => UniverseLift.lowerSimplexTensor z) hfg
      simpa only [UniverseLift.lowerSimplexTensor_simplexTensorMap] using he)
  rw [← UniverseLift.simplexTensorMap_operator, ← UniverseLift.simplexTensorMap_target,
    ← UniverseLift.simplexTensorMap_source, family_lift, family_lift]
  exact h

/-- Object evaluation is also an entire map of original small simplicial sets. -/
def point (d : D) : K.obj d ⟶ F.obj d :=
  UniverseLift.lower (NerveMovingParameter.evaluate (NerveMovingParameter.lifted.{w} K) F a d)

lemma point_lift (d : D) : UniverseLift.map.{w} (point K F a d) =
    NerveMovingParameter.evaluate (NerveMovingParameter.lifted.{w} K) F a d :=
  UniverseLift.map_lower _

lemma family_restrict (L : D ⥤ SSet.{v}) (i : L ⟶ K) {n : ℕ}
    (c : ComposableArrows D n) :
    family L F (NerveBiparameterMaps.restrict (NerveMovingParameter.lifted.{w} L)
      (NerveMovingParameter.lifted.{w} K) (NerveMovingParameter.lifted.{w} F)
      (Functor.whiskerRight i SSet.uliftFunctor.{w, v}) a) c =
      (i.app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ family K F a c := by
  apply (show Function.Injective (UniverseLift.simplexTensorMap.{w}
    (K := L.obj (c.obj 0)) (P := F.obj (c.obj (Fin.last n))) (n := n)) from
    by
      intro f g hfg
      have he := congrArg (fun z => UniverseLift.lowerSimplexTensor z) hfg
      simpa only [UniverseLift.lowerSimplexTensor_simplexTensorMap] using he)
  rw [family_lift, ← UniverseLift.simplexTensorMap_source, family_lift]
  exact uncurry_pre_app (UniverseLift.obj.{w} (F.obj (c.obj (Fin.last n))))
    (a.app (ofChain c)) (UniverseLift.map.{w} (i.app (c.obj 0)))

end SerrePositivity.SimplicialModel.NerveSmallFamilies
