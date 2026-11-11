module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeComparisonRecovery
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingNullCriterion
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationUpperNative
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationModuleInput
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated

/-!
概要：元第二対象の収縮から実逆回転対象の V 条件を導く。
方針：元 raw cone の指定比較と同じ小 Perf 包含を使い、元閉射の可逆性を反映する。
規約：対象別の収縮だけを用い、全関手 Γ の自然収縮は要求しない。
使われ方：固定厚核関手の無条件な V 因子化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C] [Small.{u} C]
  {P : Type (u + 1)} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "I" => DGFunctor.id C
local notation "L" => DGIdentityHomGluing R C
local notation "U" => DGHomGluingLoopConeBase R C C C (I) (I)
local notation "K" => dgIdentityHomGluingFunctor R C F G a h
local notation "A" => dgHomGluingInverseRotationFunctor R C C C (I) (I)
local notation "S" => dgIdentityHomGluingInverseRotationModuleSource R C F G a h
local notation "J" => dgPerfectModuleUnderlying R C
  (dgSmallPerfectEnvelopeInclusion R C ((L) ⊕ (L))
    (dgHomGluingLoopConeFamily R C C C (I) (I)))

/-- 概要：元第二対象が可縮なら元 raw 逆回転 cone は非輪状。
方針：元 Yoneda の収縮を同じ全比較の成分で移送し H⁰ の零性を使う。
規約：元の raw cone と比較を保持。使われ方：元比較射の準同型判定。 -/
lemma dgIdentityInverseRotationModuleSource_acyclic (x : P)
    (hG : ∃ t : GradedHom R (G.obj x) (G.obj x) (-1),
      (homObject R C (G.obj x) (G.obj x)).d (-1) 0 t = (unitElement R (G.obj x)).val) :
    moduleAcyclic R C (ForgetEnrichment.of (Complex R) ((S).obj x)) := by
  obtain ⟨t, dt⟩ := hG
  let Y := dgYoneda R C
  have hz := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_contractingElement_isZeroVertex _ ((Y.map _ _).f (-1) t)
    (Y.map_contractingElement R _ t dt)
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
    (dgIdentityHomGluingInverseRotationStrictNerveComparison R C F G a h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at e
  obtain ⟨s, ds⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_exists_contractingElement_of_isTerminalVertex _
    (hz.2.of_vertexIso e.symm)
  have hs := DGQuotient.homotopy_isZero_of_unit_boundary R (RightModule R C) _ s ds
  apply (moduleHomotopyAcyclic_obj_iff R C _).1
  exact (moduleHomotopyAcyclic R C).prop_of_isZero hs

/-- 概要：同じ実逆回転対象は元 cone 可縮対象の充満圏 V に入る。
方針：元 raw cone の非輪状性と指定入力同型から準同型性を得て全包含で反映する。
規約：元閉射と元小模型を保持。使われ方：上指定二単体の実因子化条件。 -/
lemma dgIdentityInverseRotation_nullProperty (x : P)
    (hG : ∃ t : GradedHom R (G.obj x) (G.obj x) (-1),
      (homObject R C (G.obj x) (G.obj x)).d (-1) 0 t = (unitElement R (G.obj x)).val) :
    dgIdentityHomGluingNullProperty R (U) ((A).obj ((K).obj x)) := by
  have hS := dgIdentityInverseRotationModuleSource_acyclic R C F G a h x hG
  have hC : moduleAcyclic R C
      (moduleCone R C (dgHomGluingInverseRotationModuleMap R C C C (I) (I) ((K).obj x))) := by
    apply (moduleHomotopyAcyclic_obj_iff R C _).1
    exact (moduleHomotopyAcyclic R C).prop_of_iso
      ((moduleToHomotopy R C).mapIso
        (dgIdentityHomGluingInverseRotationModuleInputIso R C F G a h x))
      ((moduleHomotopyAcyclic_obj_iff R C _).2 hS)
  have hq := (moduleQuasiIso_iff_acyclic_cone R C _).2 hC
  apply dgIdentityHomGluingNullProperty_of_targetImageQuasiIso R (U) C (J)
  · intro b c
    change IsIso (𝟙 _)
    infer_instance
  · intro b
    exact b.val.property.1
  · have he : (J).onClosed.map
        (dgHomGluingTargetMap R (U) (U) (U) (DGFunctor.id (U)) (DGFunctor.id (U))
          ((A).obj ((K).obj x))) =
        dgHomGluingInverseRotationModuleMap R C C C (I) (I) ((K).obj x) := by
      have ht : dgHomGluingTargetMap R (U) (U) (U)
          (DGFunctor.id (U)) (DGFunctor.id (U)) ((A).obj ((K).obj x)) =
          dgHomGluingInverseRotationMap R C C C (I) (I) ((K).obj x) :=
        dgHomGluingTargetMap_comparisonObject R (U) (U) (U)
          (DGFunctor.id (U)) (DGFunctor.id (U))
          (dgHomGluingLoopConeSmall R C C C (I) (I))
          (dgHomGluingLoopConeShiftedTarget R C C C (I) (I))
          (dgHomGluingInverseRotationMap R C C C (I) (I)) ((K).obj x)
      rw [ht]
      exact dgSmallPerfectEnvelopeComparisonMap_module R C _ _ _ _ _ _ _ _ _ _
    rwa [he]

end SerrePositivity.KST.SConstruction
