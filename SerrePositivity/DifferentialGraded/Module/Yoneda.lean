module
public import SerrePositivity.DifferentialGraded.Module.Action

/-! # 右代表 dg 加群の全次数 Yoneda -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 値 K→M(x) から代表加群の Hom 族への chain map を作る。 -/
def yonedaExtensionApp (x : D) (M : RightModule A D) {K : Complex A}
    (ψ : K ⟶ M.obj (op x)) (y : Dᵒᵖ) :
    K ⟶ homComplex A ((representable A x).obj y) (M.obj y) :=
  curryRight ((ψ ⊗ₘ M.map (op x) y) ≫ evaluation (M.obj (op x)) (M.obj y))

/-- Yoneda 拡張の斉次公式。左 tensor 評価の Koszul 符号を保持する。 -/
lemma yonedaExtensionApp_apply (x : D) (M : RightModule A D) {K : Complex A}
    (ψ : K ⟶ M.obj (op x)) (y : Dᵒᵖ) (k q n : ℤ) (hn : q + k = n)
    (t : K.X k) (h : GradedHom A y.unop x q) :
    ((yonedaExtensionApp A x M ψ y).f k t).v q n hn h =
      (k * q).negOnePow • moduleAction A M (x := op x) (y := y) h
        (ψ.f k t) (by omega) := by
  change (evaluation _ _).f n
    ((ψ ⊗ₘ M.map (op x) y).f n
      (ιTensorObj K (op x ⟶[Complex A] y) k q n (by omega) (t ⊗ₜ[A] h))) = _
  rw [tensorMap_apply, evaluation_apply]
  rfl

/-- 右代表の作用と加群作用の整合性。二つの opposite 符号が消える。 -/
lemma moduleAction_representable (x : D) (M : RightModule A D) (y z : Dᵒᵖ)
    (p q k m n s : ℤ) (hm : q + p = m) (hs : k + q = s) (hn : k + m = n)
    (f : GradedHom A y z p) (h : GradedHom A y.unop x q)
    (t : (M.obj (op x)).X k) :
    moduleAction A M (x := op x) (y := z)
      (moduleAction A (representable A x) f h hm) t hn =
    moduleAction A M f (moduleAction A M (x := op x) (y := y) h t hs) (by omega) := by
  change moduleAction A M (x := op x) (y := z)
    (forward A (x := z.unop) (y := y.unop) (z := x) f h (by omega)) t hn = _
  have ho := opposite_forward A D (op x) y z q p m hm h f
  have he := moduleAction_forward A M (x := op x) (y := y) (z := z)
    h f t hm hs hn
  rw [ho] at he
  unfold moduleAction at he ⊢
  simp only [Units.smul_def, map_zsmul] at he
  change (q * p).negOnePow •
    (((M.map (op x) z).f m
      (forward A (x := z.unop) (y := y.unop) (z := x) f h (by omega))).v k n hn t) =
    (q * p).negOnePow • _ at he
  exact smul_left_cancel (q * p).negOnePow he

/-- Yoneda 拡張は全豊穣 Hom に対して自然。 -/
lemma yonedaExtensionApp_naturality (x : D) (M : RightModule A D) {K : Complex A}
    (ψ : K ⟶ M.obj (op x)) (y z : Dᵒᵖ) :
    (β_ K (y ⟶[Complex A] z)).hom ≫
      ((representable A x).map y z ⊗ₘ yonedaExtensionApp A x M ψ z) ≫
        enrichedComposition _ _ _ =
      (yonedaExtensionApp A x M ψ y ⊗ₘ M.map y z) ≫ enrichedComposition _ _ _ := by
  apply moduleParamNaturality_of_apply
  intro y z k p q n hn t f h
  rw [yonedaExtensionApp_apply, yonedaExtensionApp_apply]
  change (k * (q + p)).negOnePow •
    moduleAction A M (x := op x) (y := z)
      (moduleAction A (representable A x) f h rfl) (ψ.f k t) (by omega) =
    (k * p).negOnePow • moduleAction A M f
      ((k * q).negOnePow • moduleAction A M (x := op x) (y := y) h (ψ.f k t)
        (by omega)) (by omega)
  have hx := moduleAction_representable A x M y z p q k (q + p) n (q + k)
    rfl (by omega) (by omega) f h (ψ.f k t)
  calc
    _ = (k * (q + p)).negOnePow •
        moduleAction A M f (moduleAction A M (x := op x) (y := y) h
          (ψ.f k t) (by omega)) (by omega) := congrArg (fun v => (k * (q + p)).negOnePow • v) hx
    _ = _ := by
      have hs : (k * (q + p)).negOnePow =
          (k * p).negOnePow * (k * q).negOnePow := by
        rw [← Int.negOnePow_add]
        congr 1
        ring
      rw [hs]
      unfold moduleAction
      simp only [Units.smul_def, map_zsmul, smul_smul, Units.val_mul]

/-- K パラメータ付き Yoneda 拡張。 -/
def yonedaExtension (x : D) (M : RightModule A D) {K : Complex A}
    (ψ : K ⟶ M.obj (op x)) : ModuleParamTrans A D K (representable A x) M where
  app := yonedaExtensionApp A x M ψ
  naturality := yonedaExtensionApp_naturality A x M ψ
/-- 代表の単位元で自然変換の成分族を評価する chain map。 -/
def yonedaEvaluateFamily (x : D) (M : RightModule A D) {K : Complex A}
    (σ : ∀ y : Dᵒᵖ, K ⟶ homComplex A ((representable A x).obj y) (M.obj y)) :
    K ⟶ M.obj (op x) :=
  (ρ_ K).inv ≫ (𝟙 K ⊗ₘ eId (Complex A) x) ≫ uncurryRight (σ (op x))

/-- 単位元での評価の全次数公式。 -/
lemma yonedaEvaluateFamily_apply (x : D) (M : RightModule A D) {K : Complex A}
    (σ : ∀ y : Dᵒᵖ, K ⟶ homComplex A ((representable A x).obj y) (M.obj y))
    (k : ℤ) (t : K.X k) :
    (yonedaEvaluateFamily A x M σ).f k t =
      ((σ (op x)).f k t).v 0 k (by omega) (unitElement A x).val := by
  have hv := congr($(rightUnitor'_inv K k).hom t)
  change (ρ_ K).inv.f k t =
    ιTensorObj K (𝟙_ (Complex A)) k 0 k (add_zero k) (t ⊗ₜ[A] (1 : A)) at hv
  change (uncurryRight (σ (op x))).f k
    ((𝟙 K ⊗ₘ eId (Complex A) x).f k ((ρ_ K).inv.f k t)) = _
  rw [hv, tensorMap_apply, uncurryRight_apply]
  rfl

/-- Yoneda 拡張を単位元で評価すると元の値に戻る。 -/
lemma yonedaEvaluate_extension (x : D) (M : RightModule A D) {K : Complex A}
    (ψ : K ⟶ M.obj (op x)) :
    yonedaEvaluateFamily A x M (yonedaExtensionApp A x M ψ) = ψ := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  rw [yonedaEvaluateFamily_apply, yonedaExtensionApp_apply]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact moduleAction_unit A M (op x) k (ψ.f k t)

/-- 全次数自然性を持つ成分族は単位での評価から復元できる。 -/
lemma yonedaExtensionApp_restore (x : D) (M : RightModule A D) {K : Complex A}
    (σ : ∀ y : Dᵒᵖ, K ⟶ homComplex A ((representable A x).obj y) (M.obj y))
    (hnat : ∀ y z : Dᵒᵖ, (β_ K (y ⟶[Complex A] z)).hom ≫
      ((representable A x).map y z ⊗ₘ σ z) ≫ enrichedComposition _ _ _ =
        (σ y ⊗ₘ M.map y z) ≫ enrichedComposition _ _ _) (y : Dᵒᵖ) :
    yonedaExtensionApp A x M (yonedaEvaluateFamily A x M σ) y = σ y := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change ((yonedaExtensionApp A x M (yonedaEvaluateFamily A x M σ) y).f k t).v
    q n hn h = _
  rw [yonedaExtensionApp_apply, yonedaEvaluateFamily_apply]
  have he := moduleParamNaturality_apply_of_sum A σ hnat
    (x := op x) (y := y) (r := 0)
    (m := k + q) (n := n) (s := q) (l := k)
    t h (unitElement A x).val rfl (by omega) (zero_add q) (zero_add k)
  change ((σ y).f k t).v q n hn
      (forward A (x := y.unop) (y := x) (z := x) h (unitElement A x).val
        (add_zero q)) = _ at he
  rw [unit_forward A h] at he
  exact he.symm


/-- 全次数自然変換は単位元での値から復元できる。 -/
lemma yonedaExtension_evaluate (x : D) (M : RightModule A D) {K : Complex A}
    (τ : ModuleParamTrans A D K (representable A x) M) :
    yonedaExtension A x M (yonedaEvaluateFamily A x M τ.app) = τ := by
  apply GradedNatTrans.ext
  funext y
  exact yonedaExtensionApp_restore A x M τ.app τ.naturality y

/-- 任意パラメータ複体での全次数 dg Yoneda 同値。 -/
def dgYonedaEquiv (x : D) (M : RightModule A D) (K : Complex A) :
    ModuleParamTrans A D K (representable A x) M ≃ (K ⟶ M.obj (op x)) where
  toFun τ := yonedaEvaluateFamily A x M τ.app
  invFun := yonedaExtension A x M
  left_inv := yonedaExtension_evaluate A x M
  right_inv := yonedaEvaluate_extension A x M
/-- Yoneda 拡張はパラメータ複体の射での前合成と可換。 -/
lemma yonedaExtensionApp_precomp (x : D) (M : RightModule A D) {K L : Complex A}
    (g : L ⟶ K) (ψ : K ⟶ M.obj (op x)) (y : Dᵒᵖ) :
    yonedaExtensionApp A x M (g ≫ ψ) y = g ≫ yonedaExtensionApp A x M ψ y := by
  dsimp only [yonedaExtensionApp]
  rw [← curryRight_naturality_source, tensorHom_comp_tensorHom_assoc]
  simp

/-- 単位での評価はパラメータ複体の射での前合成と可換。 -/
lemma yonedaEvaluateFamily_precomp (x : D) (M : RightModule A D) {K L : Complex A}
    (g : L ⟶ K)
    (σ : ∀ y : Dᵒᵖ, K ⟶ homComplex A ((representable A x).obj y) (M.obj y)) :
    yonedaEvaluateFamily A x M (fun y => g ≫ σ y) = g ≫ yonedaEvaluateFamily A x M σ := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  rw [yonedaEvaluateFamily_apply]
  change ((σ (op x)).f k (g.f k t)).v 0 k (by omega) (unitElement A x).val =
    (yonedaEvaluateFamily A x M σ).f k (g.f k t)
  rw [yonedaEvaluateFamily_apply]

/-- dg Yoneda の Hom 複体そのものの同型。H⁰ のみの同値ではない。 -/
def dgYonedaIso [Small.{u} D] (x : D) (M : RightModule A D) :
    moduleHom A D (representable A x) M ≅ M.obj (op x) where
  hom := yonedaEvaluateFamily A x M
    (fun y => moduleHomπ A D (representable A x) M y.unop)
  inv := (moduleHomEquiv A D (M.obj (op x)) (representable A x) M).symm
    (yonedaExtension A x M (𝟙 _))
  hom_inv_id := by
    apply moduleHom_ext
    intro y
    rw [Category.assoc, moduleHomEquiv_symm_π]
    change _ ≫ yonedaExtensionApp A x M (𝟙 _) (op y) = _
    rw [← yonedaExtensionApp_precomp]
    simp only [Category.comp_id]
    have hr := yonedaExtensionApp_restore A x M
      (fun y => moduleHomπ A D (representable A x) M y.unop)
      (moduleHomπ_naturality A D (representable A x) M) (op y)
    exact hr
  inv_hom_id := by
    rw [← yonedaEvaluateFamily_precomp]
    have hp : ∀ y : Dᵒᵖ,
        (moduleHomEquiv A D (M.obj (op x)) (representable A x) M).symm
          (yonedaExtension A x M (𝟙 _)) ≫ moduleHomπ A D (representable A x) M y.unop =
        yonedaExtensionApp A x M (𝟙 _) y := by
      intro y
      exact moduleHomEquiv_symm_π A D _ _ _ _ _
    simp_rw [hp]
    exact yonedaEvaluate_extension A x M (𝟙 _)
end SerrePositivity.DifferentialGraded
