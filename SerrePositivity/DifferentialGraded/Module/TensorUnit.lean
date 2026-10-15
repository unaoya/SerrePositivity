module
public import SerrePositivity.DifferentialGraded.Module.TensorAdjunction
public import SerrePositivity.DifferentialGraded.Module.Isomorphism
public import SerrePositivity.DifferentialGraded.Module.HomFunctor

/-! # tensor 加群の左単位とパラメータ射の逆転置 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- Hom の閉単位の逆転置は既存の左 unitor。 -/
lemma uncurryRight_identity (P : Complex A) :
    uncurryRight (identity P) = (λ_ P).hom := by
  apply (cancel_epi (λ_ P).inv).1
  rw [Iso.inv_hom_id]
  apply HomologicalComplex.Hom.ext
  funext i
  change (leftUnitor' P).inv i ≫ (uncurryRight (identity P)).f i = 𝟙 (P.X i)
  rw [leftUnitor'_inv]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change (uncurryRight (identity P)).f i
    (ιTensorObj (𝟙_ (Complex A)) P 0 i i (zero_add i) ((1 : A) ⊗ₜ[A] v)) = v
  rw [uncurryRight_apply]
  change ((cycleFromUnit _ (identity P)).val.v i i (by omega)) v = v
  simp only [identity, cycleFromUnit_unitFromCycle, Cochain.ofHom_v]
  rfl

/-- 通常射の閉零要素を逆転置すると左単位の後の通常射。 -/
lemma uncurryRight_closedMap {P Q : Complex A} (f : P ⟶ Q) :
    uncurryRight (closedMap A f) = (λ_ P).hom ≫ f := by
  apply (cancel_epi (λ_ P).inv).1
  rw [Iso.inv_hom_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext i
  change (leftUnitor' P).inv i ≫ (uncurryRight (closedMap A f)).f i = f.f i
  rw [leftUnitor'_inv]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change (uncurryRight (closedMap A f)).f i
    (ιTensorObj (𝟙_ (Complex A)) P 0 i i (zero_add i) ((1 : A) ⊗ₜ[A] v)) = f.f i v
  rw [uncurryRight_apply]
  change ((cycleFromUnit _ (closedMap A f)).val.v i i (by omega)) v = f.f i v
  rw [closedMap_cycle, Cochain.ofHom_v]

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 dg 自然な左単位比較。 -/
def moduleTensorUnitIso (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) (tensorModule (𝟙_ (Complex A)) M) ≅
      ForgetEnrichment.of (Complex A) M :=
  moduleIsoMk A D (fun x => λ_ (M.obj x)) (by
    intro x y
    have h := tensorFamilyUncurry_naturality A
      (fun z : Dᵒᵖ => identity (M.obj z)) (moduleIdentity_naturality A M) x y
    simpa only [uncurryRight_identity] using h)

@[simp] lemma moduleTensorUnitIso_hom_eval (M : RightModule A D) (x : D) :
    (moduleEvaluation A D x).map (moduleTensorUnitIso A D M).hom = (λ_ (M.obj (op x))).hom :=
  moduleIsoMk_hom_eval A D _ _ x

@[simp] lemma moduleTensorUnitIso_inv_eval (M : RightModule A D) (x : D) :
    (moduleEvaluation A D x).map (moduleTensorUnitIso A D M).inv = (λ_ (M.obj (op x))).inv :=
  moduleIsoMk_inv_eval A D _ _ x

/-- Hom end への chain map を、tensor 加群からの閉零射へ逆転置する。 -/
def moduleParamUncurry {K : Complex A} {M N : RightModule A D}
    (a : K ⟶ moduleHom A D M N) :
    ForgetEnrichment.of (Complex A) (tensorModule K M) ⟶ ForgetEnrichment.of (Complex A) N :=
  (moduleMapFamilyEquiv A D _ _).symm
    (tensorFamilyUncurry A ((moduleHomEquiv A D K M N) a))

@[simp] lemma moduleParamUncurry_eval {K : Complex A} {M N : RightModule A D}
    (a : K ⟶ moduleHom A D M N) (x : D) :
    (moduleEvaluation A D x).map (moduleParamUncurry A D a) =
      uncurryRight (a ≫ moduleHomπ A D M N x) := by
  rw [moduleParamUncurry]
  exact moduleMorphismMk_eval A D _ _ x

/-- パラメータの前合成と tensor 加群からの射の前合成は一致する。 -/
lemma moduleParamUncurry_precomp {K L : Complex A} {M N : RightModule A D}
    (g : K ⟶ L) (a : L ⟶ moduleHom A D M N) :
    tensorModuleMap g M ≫ moduleParamUncurry A D a = moduleParamUncurry A D (g ≫ a) := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, tensorModuleMap_eval,
    moduleParamUncurry_eval, moduleParamUncurry_eval]
  apply (tensorRightHomEquiv _ _ _).injective
  change curryRight ((g ⊗ₘ 𝟙 _) ≫ uncurryRight (a ≫ moduleHomπ A D M N x)) =
    curryRight (uncurryRight ((g ≫ a) ≫ moduleHomπ A D M N x))
  rw [curryRight_naturality_source, curryRight_uncurryRight, curryRight_uncurryRight,
    Category.assoc]

/-- 単位パラメータの逆転置は左単位比較と元の閉零射の合成。 -/
lemma moduleParamUncurry_closed {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleParamUncurry A D
      (ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f) =
    (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).hom ≫ f := by
  apply moduleMorphism_ext
  intro x
  rw [moduleParamUncurry_eval, CategoryTheory.Functor.map_comp,
    moduleTensorUnitIso_hom_eval, ← moduleEvaluation_closedMap, uncurryRight_closedMap]

end SerrePositivity.DifferentialGraded
