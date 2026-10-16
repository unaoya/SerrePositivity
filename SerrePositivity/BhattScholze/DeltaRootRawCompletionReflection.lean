module

public import SerrePositivity.BhattScholze.DeltaRootRawCompletionRestriction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerComplete

/-! # raw根環の実逐次完備化H0の二座標反射 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "a" => (c (p : A))
local notation "z" => (c d)
local notation "M" => CategoryTheory.Functor.obj
  (DerivedCategory.singleFunctor (ModuleCat Raw) 0) (ModuleCat.of Raw Raw)
local notation "Cp" => derivedComplexCompletionFunctor Raw a
local notation "Y" => CategoryTheory.Functor.obj (derivedComplexCompletionFunctor Raw a) M
local notation "Z" => DeltaRootRawInternalIteratedCompletion D d b
local notation "H" => CategoryTheory.Functor.obj (DerivedCategory.homologyFunctor (ModuleCat Raw) 0)
local notation "U" => CategoryTheory.NatTrans.app (derivedComplexCompletionUnit Raw a) M ≫
  CategoryTheory.NatTrans.app (derivedComplexCompletionUnit Raw z) Y

/-- raw自身の実逐次完備化から誘導される、元のRaw線形標準単位。 -/
def deltaRootRawInternalH0Unit : Raw →ₗ[Raw] H Z :=
  (((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Raw) 0).inv.app
    (ModuleCat.of Raw Raw)) ≫ (DerivedCategory.homologyFunctor (ModuleCat Raw) 0).map U).hom

/-- raw自身の実逐次対象は、二つ目の完備化後にも最初の座標について完備。 -/
theorem deltaRootRawInternalIterated_isComplete_first : IsComplete Raw a Z := by
  have hY : IsComplete Raw a Y := derivedComplexCompletionFunctor_isComplete Raw a M
  let K := DerivedCategory.Q.objPreimage Y
  let eK : DerivedCategory.Q.obj K ≅ Y := DerivedCategory.Q.objObjPreimageIso Y
  have hK := isComplete_of_iso Raw a eK.symm hY
  have hstage (n : ℕ) : IsComplete Raw a
      (DerivedCategory.Q.obj (complexPowerKoszulStage Raw z K n)) :=
    isComplete_Q_mappingCone Raw a (smulId (z ^ n) K) hK hK
  have hC := isComplete_complexTowerHomotopyLimitObject_of_stages Raw a
    (complexPowerKoszulStage Raw z K) (complexPowerKoszulTransition Raw z K) hstage
  let e : complexCompletionObject Raw z K ≅ Z :=
    (derivedComplexCompletionComparison Raw z).symm.app K ≪≫
      (derivedComplexCompletionFunctor Raw z).mapIso eK
  exact isComplete_of_iso Raw a e hC

/-- raw自身の実逐次H0は両座標について導来完備。 -/
theorem deltaRootRawInternalH0_isComplete :
    ∀ j : Fin 2, IsModuleComplete Raw (pairKoszulCoordinates Raw a z j) (H Z) := by
  intro j
  fin_cases j
  · exact isComplete_homology_isModuleComplete Raw a Z
      (deltaRootRawInternalIterated_isComplete_first D d b) 0
  · exact derivedComplexCompletionFunctor_homology_isModuleComplete Raw z Y 0

/-- 同じ標準単位は、両座標について完備な加群への写像を一意に決定する。 -/
theorem deltaRootRawInternalH0_isCompleteModuleReflection :
    IsCompleteModuleReflection Raw (pairKoszulCoordinates Raw a z) (H Z)
      (deltaRootRawInternalH0Unit D d b 1) where
  isComplete := deltaRootRawInternalH0_isComplete D d b
  universal N hN := by
    have hp : IsModuleComplete Raw a N := by simpa [pairKoszulCoordinates] using hN 0
    have hd : IsModuleComplete Raw z N := by
      simpa only [pairKoszulCoordinates, Fin.snoc_last] using hN (Fin.last 1)
    have hM : (M).IsLE 0 := inferInstance
    let := hM
    let := derivedComplexCompletionFunctor_isLE Raw a M 0 hM
    let eqv := ModuleCat.homEquiv.symm |>.trans
      (completionH0HomEquiv Raw z Y N hd) |>.trans
      (completionH0HomEquiv Raw a M N hp) |>.trans
      (Iso.homCongr
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Raw) 0).app
          (ModuleCat.of Raw Raw)) (Iso.refl N)) |>.trans
      ModuleCat.homEquiv |>.trans (LinearMap.ringLmapEquivSelf Raw Raw N).toEquiv
    have he (g : H Z →ₗ[Raw] N) : eqv g = g (deltaRootRawInternalH0Unit D d b 1) := by
      simp only [eqv, Equiv.trans_apply, completionH0HomEquiv_apply,
        Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
      simp only [deltaRootRawInternalH0Unit, Functor.map_comp]
      rfl
    have hf : (eqv : _ → _) = (fun g => g (deltaRootRawInternalH0Unit D d b 1)) := funext he
    rw [← hf]
    exact eqv.bijective

/-- 二つの実H0反射の間には、元の線形標準単位を保つ同型がある。 -/
theorem exists_deltaRootRawInternalPDLinearEquiv :
    ∃ e : H Z ≃ₗ[Raw] PDCompletionH0 Raw p z,
      ∀ x : Raw, e (deltaRootRawInternalH0Unit D d b x) =
        koszulCompletionH0Unit Raw (pairKoszulCoordinates Raw (p : Raw) z) x := by
  let B := ModuleCat.of Raw (PDCompletionH0 Raw p z)
  let u := koszulCompletionH0Unit Raw (pairKoszulCoordinates Raw (p : Raw) z)
  let v := deltaRootRawInternalH0Unit D d b
  let h := deltaRootRawInternalH0_isCompleteModuleReflection D d b
  have hB : IsCompleteModuleReflection Raw (pairKoszulCoordinates Raw a z) B (u 1) := by
    simpa only [map_natCast] using pairCompletionH0_isCompleteModuleReflection Raw (p : Raw) z
  obtain ⟨f, hf⟩ := (h.universal B hB.isComplete).surjective (u 1)
  obtain ⟨g, hg⟩ := (hB.universal (H Z) h.isComplete).surjective (v 1)
  change f (v 1) = u 1 at hf
  change g (u 1) = v 1 at hg
  have hgf : g.comp f = LinearMap.id := by
    apply (h.universal (H Z) h.isComplete).injective
    change g (f (v 1)) = v 1
    rw [hf, hg]
  have hfg : f.comp g = LinearMap.id := by
    apply (hB.universal B hB.isComplete).injective
    change f (g (u 1)) = u 1
    rw [hg, hf]
  let e : H Z ≃ₗ[Raw] PDCompletionH0 Raw p z :=
    { f with
      invFun := g
      left_inv := fun x => LinearMap.congr_fun hgf x
      right_inv := fun x => LinearMap.congr_fun hfg x }
  refine ⟨e, ?_⟩
  intro x
  have hx : v x = x • v 1 := by simpa only [smul_eq_mul, mul_one] using v.map_smul x (1 : Raw)
  have hu : u x = x • u 1 := by simpa only [smul_eq_mul, mul_one] using u.map_smul x (1 : Raw)
  change e (v x) = u x
  rw [hx, hu, map_smul]
  exact congrArg (fun t => x • t) hf

/-- 元のRaw線形単位で正規化した、実逐次H0から実PD完備化H0への同型。 -/
def deltaRootRawInternalPDLinearEquiv : H Z ≃ₗ[Raw] PDCompletionH0 Raw p z :=
  (exists_deltaRootRawInternalPDLinearEquiv D d b).choose

/-- 比較は全raw係数の元の完備化像を保つ。 -/
theorem deltaRootRawInternalPDLinearEquiv_unit (x : Raw) :
    deltaRootRawInternalPDLinearEquiv D d b (deltaRootRawInternalH0Unit D d b x) =
      koszulCompletionH0Unit Raw (pairKoszulCoordinates Raw (p : Raw) z) x :=
  (exists_deltaRootRawInternalPDLinearEquiv D d b).choose_spec x

/-- 元の実根添加源の実H0とrawのPD完備化H0の具体的A線形同型。 -/
def deltaRootSourcePDH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (DeltaRootSourceIteratedPDCompletion D d b).obj ≅
      (ModuleCat.restrictScalars c).obj (ModuleCat.of Raw (PDCompletionH0 Raw p z)) :=
  deltaRootSourceInternalRawH0Iso D d b ≪≫
    (ModuleCat.restrictScalars c).mapIso (deltaRootRawInternalPDLinearEquiv D d b).toModuleIso

end SerrePositivity.BhattScholze
