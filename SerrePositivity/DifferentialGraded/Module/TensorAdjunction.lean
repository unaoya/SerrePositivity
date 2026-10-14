module
public import SerrePositivity.DifferentialGraded.Module.Free
public import SerrePositivity.DifferentialGraded.Module.Yoneda

/-! # tensor した右 dg 加群の閉射の転置 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- tensor 加群からの全次数自然な閉射族を K パラメータ付き自然変換へ転置する。 -/
def tensorFamilyCurry {K : Complex A} {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, (tensorModule K M).obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, (tensorModule K M).map x y ≫
      homPostcompose ((tensorModule K M).obj x) (a y) =
        N.map x y ≫ homPrecompose (a x) (N.obj y)) :
    ModuleParamTrans A D K M N where
  app x := curryRight (a x)
  naturality x y := by
    apply moduleParamNaturality_of_apply A (M := M) (N := N) (fun x => curryRight (a x))
    intro x y k p r n hn t f v
    change (a y).f n (ιTensorObj K (M.obj y) k (r + p) n (by omega)
      (t ⊗ₜ[A] moduleAction A M f v rfl)) =
      (k * p).negOnePow • moduleAction A N f
        ((a x).f (r + k) (ιTensorObj K (M.obj x) k r (r + k) (by omega)
          (t ⊗ₜ[A] v))) (by omega)
    have hh := closedFamily_action A (M := tensorModule K M) (N := N) a h x y
      p (r + k) n (by omega) f
      (ιTensorObj K (M.obj x) k r (r + k) (by omega) (t ⊗ₜ[A] v))
    rw [tensorModule_action K M x y p k r (r + k) (r + p) n
      (by omega) rfl (by omega)] at hh
    simp only [Units.smul_def, map_zsmul] at hh
    change (p * k).negOnePow • (a y).f n
      (ιTensorObj K (M.obj y) k (r + p) n (by omega)
        (t ⊗ₜ[A] moduleAction A M f v rfl)) = _ at hh
    have he := congrArg (fun z => (k * p).negOnePow • z) hh
    rw [mul_comm p k, smul_smul, Int.units_mul_self, one_smul] at he
    exact he
/-- パラメータ付き全次数自然性を逆転置した閉射族は再び全次数自然。 -/
lemma tensorFamilyUncurry_naturality {K : Complex A} {M N : RightModule A D}
    (σ : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (h : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ σ y) ≫ enrichedComposition _ _ _ =
        (σ x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _) (x y : Dᵒᵖ) :
    (tensorModule K M).map x y ≫ homPostcompose ((tensorModule K M).obj x)
      (uncurryRight (σ y)) =
    N.map x y ≫ homPrecompose (uncurryRight (σ x)) (N.obj y) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (((tensorModule K M).map x y).f p f).comp
      (Cochain.ofHom (uncurryRight (σ y))) (add_zero p) =
    (Cochain.ofHom (uncurryRight (σ x))).comp ((N.map x y).f p f) (zero_add p)
  apply Cochain.ext
  intro a n hn
  apply mapBifunctor.hom_ext
  intro k r ha
  change k + r = a at ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro t v
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v]
  change (uncurryRight (σ y)).f n (moduleAction A (tensorModule K M) f
      (ιTensorObj K (M.obj x) k r a ha (t ⊗ₜ[A] v)) hn) =
    moduleAction A N f ((uncurryRight (σ x)).f a
      (ιTensorObj K (M.obj x) k r a ha (t ⊗ₜ[A] v))) hn
  rw [tensorModule_action K M x y p k r a (r + p) n ha rfl hn]
  simp only [Units.smul_def, map_zsmul]
  rw [uncurryRight_apply, uncurryRight_apply]
  have he := moduleParamNaturality_apply_of_sum A σ h (x := x) (y := y)
    (k := k) (p := p) (r := r) (m := k + p) (n := n) (s := r + p) (l := a)
    t f v rfl (by omega) rfl (by omega)
  rw [he]
  simp only [Units.smul_def, smul_smul, mul_comm p k]
  rw [← Units.val_mul, Int.units_mul_self]
  simp

/-- 豊穣自然変換を tensor 加群からの通常射族へ逆転置する。 -/
def tensorFamilyUncurry {K : Complex A} {M N : RightModule A D}
    (τ : ModuleParamTrans A D K M N) : ModuleMapFamily A D (tensorModule K M) N :=
  ⟨fun x => uncurryRight (τ.app x), tensorFamilyUncurry_naturality A τ.app τ.naturality⟩

/-- tensor 加群からの全次数自然な閉射族と K パラメータ付き自然変換の同値。 -/
def tensorFamilyEquiv (K : Complex A) (M N : RightModule A D) :
    ModuleMapFamily A D (tensorModule K M) N ≃ ModuleParamTrans A D K M N where
  toFun a := tensorFamilyCurry A a.val a.property
  invFun := tensorFamilyUncurry A
  left_inv a := by
    apply Subtype.ext
    funext x
    exact uncurryRight_curryRight (a.val x)
  right_inv τ := by
    apply GradedNatTrans.ext
    funext x
    exact curryRight_uncurryRight (τ.app x)
variable (D) [Small.{u} D]
/-- tensor 加群からの主 end の閉零射と全次数パラメータ付き自然変換の同値。 -/
def tensorClosedHomEquiv (K : Complex A) (M N : RightModule A D) :
    (ForgetEnrichment.of (Complex A) (tensorModule K M) ⟶
      ForgetEnrichment.of (Complex A) N) ≃ ModuleParamTrans A D K M N :=
  (moduleMapFamilyEquiv A D _ _).trans (tensorFamilyEquiv A K M N)

/-- 自由加群からの射を評価対象への通常 chain map に同定する。 -/
def freeHomEquiv (x : D) (K : Complex A) (N : ModuleCategory A D) :
    (((freeAt x).obj K) ⟶ N) ≃ (K ⟶ (moduleEvaluation A D x).obj N) :=
  (tensorClosedHomEquiv A D K (representable A x) (ForgetEnrichment.to (Complex A) N)).trans
    (dgYonedaEquiv A x (ForgetEnrichment.to (Complex A) N) K)
/-- 自由 Hom 同値は代表の単位元での評価として計算される。 -/
lemma freeHomEquiv_apply (x : D) (K : Complex A) (N : ModuleCategory A D)
    (f : (freeAt x).obj K ⟶ N) (k : ℤ) (t : K.X k) :
    (freeHomEquiv A D x K N f).f k t =
    ((moduleEvaluation A D x).map f).f k
      (ιTensorObj K (x ⟶[Complex A] x) k 0 k (add_zero k)
        (t ⊗ₜ[A] (unitElement A x).val)) := by
  change (yonedaEvaluateFamily A x (ForgetEnrichment.to (Complex A) N)
    (fun y => curryRight ((moduleEvaluation A D y.unop).map f))).f k t = _
  rw [yonedaEvaluateFamily_apply]
  rfl

/-- 自由 Hom 同値は生成する複体の chain map に対して自然。 -/
lemma freeHomEquiv_naturality_left (x : D) {K L : Complex A} (g : L ⟶ K)
    (N : ModuleCategory A D) (f : (freeAt x).obj K ⟶ N) :
    freeHomEquiv A D x L N ((freeAt x).map g ≫ f) = g ≫ freeHomEquiv A D x K N f := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  rw [freeHomEquiv_apply]
  rw [CategoryTheory.Functor.map_comp]
  change ((moduleEvaluation A D x).map f).f k
      (((moduleEvaluation A D x).map ((freeAt x).map g)).f k
        (ιTensorObj L (x ⟶[Complex A] x) k 0 k (add_zero k)
          (t ⊗ₜ[A] (unitElement A x).val))) =
    (freeHomEquiv A D x K N f).f k (g.f k t)
  have hg : (moduleEvaluation A D x).map ((freeAt x).map g) =
      g ⊗ₘ 𝟙 (x ⟶[Complex A] x) := tensorModuleMap_eval g (representable A x) x
  have he := congrArg (fun s : L ⊗ (x ⟶[Complex A] x) ⟶ K ⊗ (x ⟶[Complex A] x) =>
    s.f k (ιTensorObj L (x ⟶[Complex A] x) k 0 k (add_zero k)
      (t ⊗ₜ[A] (unitElement A x).val))) hg
  calc
    _ = ((moduleEvaluation A D x).map f).f k
        ((g ⊗ₘ 𝟙 (x ⟶[Complex A] x)).f k
          (ιTensorObj L (x ⟶[Complex A] x) k 0 k (add_zero k)
            (t ⊗ₜ[A] (unitElement A x).val))) :=
      congrArg (fun z => ((moduleEvaluation A D x).map f).f k z) he
    _ = ((moduleEvaluation A D x).map f).f k
        (ιTensorObj K (x ⟶[Complex A] x) k 0 k (add_zero k)
          (g.f k t ⊗ₜ[A] (unitElement A x).val)) := by
      rw [tensorMap_apply]
      rfl
    _ = (freeHomEquiv A D x K N f).f k (g.f k t) :=
      (freeHomEquiv_apply A D x K N f k (g.f k t)).symm

/-- 自由 Hom 同値は値域の加群射に対して自然。 -/
lemma freeHomEquiv_naturality_right (x : D) (K : Complex A) {N P : ModuleCategory A D}
    (f : (freeAt x).obj K ⟶ N) (h : N ⟶ P) :
    freeHomEquiv A D x K P (f ≫ h) =
      freeHomEquiv A D x K N f ≫ (moduleEvaluation A D x).map h := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  rw [freeHomEquiv_apply, CategoryTheory.Functor.map_comp]
  change ((moduleEvaluation A D x).map h).f k
    (((moduleEvaluation A D x).map f).f k
      (ιTensorObj K (x ⟶[Complex A] x) k 0 k (add_zero k)
        (t ⊗ₜ[A] (unitElement A x).val))) =
    ((moduleEvaluation A D x).map h).f k ((freeHomEquiv A D x K N f).f k t)
  rw [freeHomEquiv_apply]

/-- 任意非有界複体で生成する自由 dg 加群は評価の左随伴。 -/
def freeEvaluationAdjunction (x : D) : freeAt x ⊣ moduleEvaluation A D x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := freeHomEquiv A D x
      homEquiv_naturality_left_symm := by
        intro K L N g t
        apply (freeHomEquiv A D x K N).injective
        rw [Equiv.apply_symm_apply, freeHomEquiv_naturality_left, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro K N P f h
        exact freeHomEquiv_naturality_right A D x K f h }
end SerrePositivity.DifferentialGraded
