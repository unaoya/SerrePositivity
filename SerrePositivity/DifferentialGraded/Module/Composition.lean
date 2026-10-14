module
public import SerrePositivity.DifferentialGraded.Module.Action

/-! # dg 加群のパラメータ付き変換の合成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- パラメータ付き変換族の対象ごとの豊穣合成。 -/
def moduleComposeApp {K L : Complex A} {M N P : RightModule A D}
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (b : ∀ x : Dᵒᵖ, L ⟶ homComplex A (N.obj x) (P.obj x)) (x : Dᵒᵖ) :
    K ⊗ L ⟶ homComplex A (M.obj x) (P.obj x) :=
  (a x ⊗ₘ b x) ≫ enrichedComposition _ _ _

/-- パラメータ合成の斉次公式。 -/
lemma moduleComposeApp_apply {K L : Complex A} {M N P : RightModule A D}
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (b : ∀ x : Dᵒᵖ, L ⟶ homComplex A (N.obj x) (P.obj x)) (x : Dᵒᵖ)
    (k l m : ℤ) (hm : k + l = m) (t : K.X k) (s : L.X l) :
    (moduleComposeApp A a b x).f m
      (ιTensorObj K L k l m hm (t ⊗ₜ[A] s)) =
    (k * l).negOnePow • (((a x).f k t).comp ((b x).f l s) hm) := by
  change (enrichedComposition _ _ _).f m
    ((a x ⊗ₘ b x).f m (ιTensorObj K L k l m hm (t ⊗ₜ[A] s))) = _
  rw [tensorMap_apply, enrichedComposition_apply]

/-- 全次数自然な変換族の合成も全次数自然。 -/
lemma moduleComposeApp_naturality {K L : Complex A} {M N P : RightModule A D}
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (b : ∀ x : Dᵒᵖ, L ⟶ homComplex A (N.obj x) (P.obj x))
    (ha : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _)
    (hb : ∀ x y : Dᵒᵖ, (β_ L (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ b y) ≫ enrichedComposition _ _ _ =
        (b x ⊗ₘ P.map x y) ≫ enrichedComposition _ _ _) (x y : Dᵒᵖ) :
    (β_ (K ⊗ L) (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ moduleComposeApp A a b y) ≫ enrichedComposition _ _ _ =
      (moduleComposeApp A a b x ⊗ₘ P.map x y) ≫ enrichedComposition _ _ _ := by
  apply triple_ext
  intro k l p m hm
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro t s f
  change (enrichedComposition _ _ _).f m
    ((M.map x y ⊗ₘ moduleComposeApp A a b y).f m
      ((signedSwap (K ⊗ L) (x ⟶[Complex A] y)).hom.f m
        (ιTensorObj (K ⊗ L) (x ⟶[Complex A] y) (k + l) p m hm
          (ιTensorObj K L k l (k + l) rfl (t ⊗ₜ[A] s) ⊗ₜ[A] f)))) =
    (enrichedComposition _ _ _).f m
      ((moduleComposeApp A a b x ⊗ₘ P.map x y).f m
        (ιTensorObj (K ⊗ L) (x ⟶[Complex A] y) (k + l) p m hm
          (ιTensorObj K L k l (k + l) rfl (t ⊗ₜ[A] s) ⊗ₜ[A] f)))
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  change ((k + l) * p).negOnePow • (enrichedComposition _ _ _).f m
    ((M.map x y ⊗ₘ moduleComposeApp A a b y).f m
      (ιTensorObj (x ⟶[Complex A] y) (K ⊗ L) p (k + l) m (by omega)
        (f ⊗ₜ[A] ιTensorObj K L k l (k + l) rfl (t ⊗ₜ[A] s)))) = _
  rw [tensorMap_apply, tensorMap_apply, enrichedComposition_apply,
    enrichedComposition_apply, mul_comm p (k + l), smul_smul,
    Int.units_mul_self, one_smul]
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rw [Cochain.units_smul_v,
    Cochain.comp_v _ _ (by omega) r (r + p) n rfl (by omega),
    Cochain.comp_v _ _ hm r (r + (k + l)) n rfl (by omega),
    moduleComposeApp_apply, moduleComposeApp_apply,
    Cochain.units_smul_v, Cochain.units_smul_v,
    Cochain.comp_v _ _ rfl (r + p) (r + p + k) n rfl (by omega),
    Cochain.comp_v _ _ rfl r (r + k) (r + (k + l)) rfl (by omega)]
  change (k * l).negOnePow •
    (((b y).f l s).v (r + p + k) n (by omega)
      (((a y).f k t).v (r + p) (r + p + k) rfl (moduleAction A M f v rfl))) =
    ((k + l) * p).negOnePow • moduleAction A P f
      ((k * l).negOnePow • (((b x).f l s).v (r + k) (r + (k + l)) (by omega)
        (((a x).f k t).v r (r + k) rfl v))) (by omega)
  have h₁ := moduleParamNaturality_apply_of_sum A a ha
    (x := x) (y := y) (m := k + p) (n := r + p + k) (s := r + p) (l := r + k)
    t f v rfl (by omega) rfl rfl
  have h₂ := moduleParamNaturality_apply_of_sum A b hb
    (x := x) (y := y) (m := l + p) (n := n) (s := r + p + k) (l := r + (k + l))
    s f (((a x).f k t).v r (r + k) rfl v) rfl (by omega) (by omega) (by omega)
  rw [h₁]
  simp only [Units.smul_def, map_zsmul]
  rw [h₂]
  unfold moduleAction
  simp only [Units.smul_def, map_zsmul, smul_smul]
  change ((k * l).negOnePow * ((k * p).negOnePow * (l * p).negOnePow)) • (_ : (P.obj y).X n) =
    (((k + l) * p).negOnePow * (k * l).negOnePow) • (_ : (P.obj y).X n)
  simp only [← Int.negOnePow_add]
  congr 1
  congr 1
  ring
/-- パラメータ付き自然変換を tensor パラメータで合成する。 -/
def moduleParamCompose {K L : Complex A} {M N P : RightModule A D}
    (a : ModuleParamTrans A D K M N) (b : ModuleParamTrans A D L N P) :
    ModuleParamTrans A D (K ⊗ L) M P where
  app := moduleComposeApp A a.app b.app
  naturality := moduleComposeApp_naturality A a.app b.app a.naturality b.naturality

/-- 各対象の閉単位は全次数自然。 -/
lemma moduleIdentity_naturality (M : RightModule A D) (x y : Dᵒᵖ) :
    (β_ (𝟙_ (Complex A)) (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ identity (M.obj y)) ≫ enrichedComposition _ _ _ =
    (identity (M.obj x) ⊗ₘ M.map x y) ≫ enrichedComposition _ _ _ := by
  rw [braiding_tensorUnit_left]
  rw [tensorHom_def, Category.assoc, Category.assoc,
    ← rightUnitor_inv_naturality_assoc, comp_identity, Category.comp_id]
  rw [tensorHom_def', Category.assoc, ← leftUnitor_naturality]
  have hi := identity_comp (M.obj x) (M.obj y)
  have hi' := congrArg (fun f => (λ_ (homComplex A (M.obj x) (M.obj y))).hom ≫ f) hi
  simp only [Iso.hom_inv_id_assoc, Category.comp_id] at hi'
  rw [← hi']

/-- 単位複体パラメータを持つ恒等自然変換。 -/
def moduleParamIdentity (M : RightModule A D) :
    ModuleParamTrans A D (𝟙_ (Complex A)) M M where
  app x := identity (M.obj x)
  naturality := moduleIdentity_naturality A M

variable (D) [Small.{u} D]
/-- Hom end の閉単位。 -/
def moduleIdentity (M : RightModule A D) : 𝟙_ (Complex A) ⟶ moduleHom A D M M :=
  (moduleHomEquiv A D _ M M).symm (moduleParamIdentity A M)

/-- Hom end の豊穣合成。 -/
def moduleComposition (M N P : RightModule A D) :
    moduleHom A D M N ⊗ moduleHom A D N P ⟶ moduleHom A D M P :=
  (moduleHomEquiv A D _ M P).symm
    { app x := moduleComposeApp A
        (fun y => moduleHomπ A D M N y.unop) (fun y => moduleHomπ A D N P y.unop) x
      naturality := moduleComposeApp_naturality A _ _
        (moduleHomπ_naturality A D M N) (moduleHomπ_naturality A D N P) }

/-- 単位の成分は各対象の恒等射。 -/
@[reassoc (attr := simp)]
lemma moduleIdentity_π (M : RightModule A D) (x : D) :
    moduleIdentity A D M ≫ moduleHomπ A D M M x = identity (M.obj (op x)) :=
  moduleHomEquiv_symm_π A D _ _ _ _ _

/-- end 合成の成分は各対象の豊穣合成。 -/
@[reassoc (attr := simp)]
lemma moduleComposition_π (M N P : RightModule A D) (x : D) :
    moduleComposition A D M N P ≫ moduleHomπ A D M P x =
    (moduleHomπ A D M N x ⊗ₘ moduleHomπ A D N P x) ≫ enrichedComposition _ _ _ :=
  moduleHomEquiv_symm_π A D _ _ _ _ _
end SerrePositivity.DifferentialGraded
