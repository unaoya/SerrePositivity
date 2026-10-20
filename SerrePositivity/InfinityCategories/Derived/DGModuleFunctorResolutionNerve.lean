module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionProjections
public import SerrePositivity.InfinityCategories.Derived.DGFunctorTrivialFibration
public import SerrePositivity.InfinityCategories.Derived.DGUniverseLift
/-!
概要：出力分解 dg 圏の入力射影は、実 dg nerve の同値を与える。
方針：対象の全射性と全 Hom の次数別全射な準同型から、実自明 Kan fibration を構成する。
規約：入力対象の Small 性や元の出力の射影性を仮定しない。使われ方：一般右導来 Hom の出力移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 実入力 Hom 射影は、同じ全複体の各次数で全射。 -/
lemma dgModuleFunctorResolutionSource_degree_surjective
    (X Y : DGModuleFunctorResolutionObject R C E F) (j : ℤ) :
    Function.Surjective ((dgModuleFunctorResolutionSource R C E F).map X Y |>.f j) := by
  let d := dgModuleFunctorResolutionDifference R C E F X Y
  let b : homObject R C X.source Y.source ⟶
      homObject R C X.source Y.source ⊞ moduleHom R E X.replacement.val Y.replacement.val :=
    biprod.inl
  let p : homObject R C X.source Y.source ⊞
      moduleHom R E X.replacement.val Y.replacement.val ⟶
        homObject R C X.source Y.source := biprod.fst
  have hs : b.f j ≫ (mappingCocone.inl d).v j j (add_zero j) ≫
      (dgModuleFunctorResolutionSourceHomMap R C E F X Y).f j = 𝟙 _ := by
    change b.f j ≫ (mappingCocone.inl d).v j j (add_zero j) ≫
      ((mappingCocone.fst d).f j ≫ p.f j) = 𝟙 _
    rw [← Category.assoc ((mappingCocone.inl d).v j j (add_zero j)),
      mappingCocone.inl_v_fst_f, Category.id_comp]
    rw [← HomologicalComplex.comp_f]
    change (biprod.inl ≫ biprod.fst : homObject R C X.source Y.source ⟶ _).f j = 𝟙 _
    rw [biprod.inl_fst, HomologicalComplex.id_f]
  intro y
  refine ⟨(mappingCocone.inl d).v j j (add_zero j) (b.f j y), ?_⟩
  exact ConcreteCategory.congr_hom hs y
/-- 入力対象だけを共通宇宙へ上げた、同じ実 Hom 射影の dg 関手。 -/
def dgModuleFunctorResolutionSourceLift :
    DGFunctor R (DGModuleFunctorResolutionObject R C E F)
      (DGUniverseLift.{v, max (u + 1) w} C) :=
  (dgModuleFunctorResolutionSource R C E F).comp
    (dgUniverseLiftUp.{u, v, max (u + 1) w} R C)
/-- 共通宇宙への実入力射影も、対象上全射。 -/
lemma dgModuleFunctorResolutionSourceLift_obj_surjective :
    Function.Surjective (dgModuleFunctorResolutionSourceLift R C E F).obj := by
  rintro ⟨⟨y⟩⟩
  obtain ⟨X, rfl⟩ := dgModuleFunctorResolutionSource_obj_surjective R C E F y
  exact ⟨X, rfl⟩
/-- 宇宙持ち上げは、同じ全 Hom 鎖写像の準同型性を変えない。 -/
lemma dgModuleFunctorResolutionSourceLift_homQuasiIso :
    HomQuasiIso (dgModuleFunctorResolutionSourceLift R C E F) := by
  intro X Y
  change QuasiIso (dgModuleFunctorResolutionSourceHomMap R C E F X Y ≫ 𝟙 _)
  rw [Category.comp_id]
  exact dgModuleFunctorResolutionSource_homQuasiIso R C E F X Y
/-- 宇宙持ち上げ後も、同じ全 Hom の各次数で全射。 -/
lemma dgModuleFunctorResolutionSourceLift_degree_surjective
    (X Y : DGModuleFunctorResolutionObject R C E F) (j : ℤ) :
    Function.Surjective ((dgModuleFunctorResolutionSourceLift R C E F).map X Y |>.f j) := by
  change Function.Surjective ((dgModuleFunctorResolutionSourceHomMap R C E F X Y ≫ 𝟙 _).f j)
  rw [Category.comp_id]
  exact dgModuleFunctorResolutionSource_degree_surjective R C E F X Y j
/-- 実出力分解から入力への dg nerve の射影は、実自明 Kan fibration。 -/
lemma dgModuleFunctorResolutionSourceNerve_trivialKanFibration :
    TrivialKanFibration (dgNerve.map (dgModuleFunctorResolutionSourceLift R C E F)) :=
  dgNerve_map_trivialKanFibration_of_surjective_quasiIso _
    (dgModuleFunctorResolutionSourceLift_obj_surjective R C E F)
    (dgModuleFunctorResolutionSourceLift_degree_surjective R C E F)
    (dgModuleFunctorResolutionSourceLift_homQuasiIso R C E F)
/-- 入力対象の小ささや元の実出力の射影性を仮定しない、分解 dg nerve の実同値。 -/
theorem dgModuleFunctorResolutionSourceNerve_isQCatEquivalence :
    IsQCatEquivalence (dgNerve.map (dgModuleFunctorResolutionSourceLift R C E F)) :=
  dgNerve_map_isQCatEquivalence_of_surjective_quasiIso _
    (dgModuleFunctorResolutionSourceLift_obj_surjective R C E F)
    (dgModuleFunctorResolutionSourceLift_degree_surjective R C E F)
    (dgModuleFunctorResolutionSourceLift_homQuasiIso R C E F)
end SerrePositivity.InfinityCategories
