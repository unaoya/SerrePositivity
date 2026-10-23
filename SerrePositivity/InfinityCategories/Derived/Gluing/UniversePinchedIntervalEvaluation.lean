module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseFunctorPinchedValue
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseSimplexFamilies
public import SerrePositivity.InfinityCategories.F1.CoherentPrismEvaluation

/-! 一般宇宙の実 Hom 鎖作用の区間評価を、元 nerve の全関手像へ各切断・全時間で照合する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial

lemma dgGluingUliftPinchedInterval_evaluate (R : Type u) [CommRing R]
    (D : Type v) [DGCategory R D] (x y : D) {n : ℕ}
    (s : (DGNerve.pinchedHom R D x y) _⦋n⦌) (t : (Δ[1] : SSet.{max u v w}) _⦋n⦌) :
    (dgGluingUliftSimplexFamily.{max u v, w} 1
      (intervalMappingUncurry (pinchedHomToIntervalMappingSpace
        (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y)))).app
        (Opposite.op ⦋n⦌) (t, ULift.up s) =
      ULift.up (s.val.pullback (coherentPrismCut (SSet.stdSimplex.objEquiv t).toOrderHom)) := by
  have he := pinchedHomToIntervalMappingSpace_evaluate
    (𝟙 (InfinityCategories.pinchedHom (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y)))
    s (ULift.up t.down)
  rw [Category.id_comp] at he
  exact congrArg ULift.up he

lemma dgGluingUliftPinchedInterval_uncurry (R : Type u) [CommRing R]
    (D : Type v) [DGCategory R D] (x y : D) :
    dgGluingUliftSimplexFamily.{max u v, w} 1
        (intervalMappingUncurry (pinchedHomToIntervalMappingSpace
          (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y))) =
      intervalMappingUncurry ((uliftPinchedHomIso.{max u v, w}
        (C := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y)).hom ≫
          pinchedHomToIntervalMappingSpace _ _) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, s⟩
  have he := pinchedHomToIntervalMappingSpace_evaluate
    (uliftPinchedHomIso.{max u v, w}
      (C := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y)).hom s t
  change (intervalMappingUncurry ((uliftPinchedHomIso.{max u v, w}
      (C := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y)).hom ≫
        pinchedHomToIntervalMappingSpace _ _)).app _ (t, s) =
    ULift.up (s.down.val.pullback (coherentPrismCut (stdSimplex.objEquiv t).toOrderHom)) at he
  exact (dgGluingUliftPinchedInterval_evaluate.{u, v, w} R D x y s.down t).trans he.symm

variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [DGCategory R C] [DGCategory R D]

lemma dgGluingUniverseFunctorPinchedInterval (F : DGFunctor R C D) (x y : C) :
    (Δ[1] ◁ dgGluingUniverseHomChainMap.{u, v, w, r} (F.map x y)) ≫
        dgGluingUliftSimplexFamily.{max u w, max v r} 1
          (intervalMappingUncurry (pinchedHomToIntervalMappingSpace (X := dgNerve R D)
            (Simplex.vertex (F.obj x)) (Simplex.vertex (F.obj y)))) =
      dgGluingUliftSimplexFamily.{max u v, max w r} 1
        (intervalMappingUncurry (pinchedHomToIntervalMappingSpace (X := dgNerve R C)
          (Simplex.vertex x) (Simplex.vertex y))) ≫ dgGluingUniverseNerveMap.{u, v, w, r} F := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, s⟩
  let eC := dgGluingUliftSimplexFamily.{max u v, max w r} 1
    (intervalMappingUncurry (pinchedHomToIntervalMappingSpace (X := dgNerve R C)
      (Simplex.vertex x) (Simplex.vertex y)))
  let eD := dgGluingUliftSimplexFamily.{max u w, max v r} 1
    (intervalMappingUncurry (pinchedHomToIntervalMappingSpace (X := dgNerve R D)
      (Simplex.vertex (F.obj x)) (Simplex.vertex (F.obj y))))
  let z := (dgGluingUniverseHomChainMap.{u, v, w, r} (F.map x y)).app (Opposite.op ⦋n⦌) s
  have hd : eD.app (Opposite.op ⦋n⦌) (t, z) =
      ULift.up (z.down.val.pullback (coherentPrismCut (stdSimplex.objEquiv t).toOrderHom)) :=
    dgGluingUliftPinchedInterval_evaluate.{u, w, max v r} R D (F.obj x) (F.obj y) z.down t
  have hc : eC.app (Opposite.op ⦋n⦌) (t, s) =
      ULift.up (s.down.val.pullback (coherentPrismCut (stdSimplex.objEquiv t).toOrderHom)) :=
    dgGluingUliftPinchedInterval_evaluate.{u, v, max w r} R C x y s.down t
  change eD.app (Opposite.op ⦋n⦌) (t, z) =
    ULift.up ((eC.app (Opposite.op ⦋n⦌) (t, s)).down.map F)
  rw [hd, hc]
  apply ULift.ext
  have hz := dgGluingUniverseFunctorPinchedValue.{u, v, w, r} F s
  change z.down.val = s.down.val.map F at hz
  rw [hz]
  apply Simplex.ext
  exact (SimplexData.map_pullback s.down.val.toSimplexData F _).symm

end SerrePositivity.InfinityCategories
