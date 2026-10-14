module
public import SerrePositivity.DifferentialGraded.Module.TensorAdjunction

/-! # 自由加群の全次数 Hom 複体 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 代表の単位を用いた K→K⊗Hom_D(x,x) の chain map。 -/
def freeUnitInsert (x : D) (K : Complex A) : K ⟶ K ⊗ (x ⟶[Complex A] x) :=
  (ρ_ K).inv ≫ (𝟙 K ⊗ₘ eId (Complex A) x)

/-- 自由生成元の単位挿入の斉次公式。 -/
lemma freeUnitInsert_apply (x : D) (K : Complex A) (k : ℤ) (t : K.X k) :
    (freeUnitInsert A x K).f k t =
    ιTensorObj K (x ⟶[Complex A] x) k 0 k (add_zero k)
      (t ⊗ₜ[A] (unitElement A x).val) := by
  have hv := congr($(rightUnitor'_inv K k).hom t)
  change (ρ_ K).inv.f k t =
    ιTensorObj K (𝟙_ (Complex A)) k 0 k (add_zero k) (t ⊗ₜ[A] (1 : A)) at hv
  change (𝟙 K ⊗ₘ eId (Complex A) x).f k ((ρ_ K).inv.f k t) = _
  rw [hv, tensorMap_apply]
  rfl

/-- 任意全次数 Hom(K,M(x)) から自由加群の Hom 成分への chain map。 -/
def freeExtensionApp (x : D) (K : Complex A) (M : RightModule A D) (y : Dᵒᵖ) :
    homComplex A K (M.obj (op x)) ⟶ homComplex A ((freeModule x K).obj y) (M.obj y) :=
  curryRight ((α_ (homComplex A K (M.obj (op x))) K (y.unop ⟶[Complex A] x)).inv ≫
    (uncurryRight (𝟙 (homComplex A K (M.obj (op x)))) ⊗ₘ M.map (op x) y) ≫
      evaluation (M.obj (op x)) (M.obj y))

/-- 自由 Hom 拡張の斉次公式。符号は出力の M(x) 次数と作用の次数の積。 -/
lemma freeExtensionApp_apply (x : D) (K : Complex A) (M : RightModule A D) (y : Dᵒᵖ)
    (s k q r n : ℤ) (hr : k + q = r) (hn : r + s = n)
    (f : Homogeneous K (M.obj (op x)) s) (t : K.X k)
    (h : GradedHom A y.unop x q) :
    ((freeExtensionApp A x K M y).f s f).v r n hn
      (ιTensorObj K (y.unop ⟶[Complex A] x) k q r hr (t ⊗ₜ[A] h)) =
    ((s + k) * q).negOnePow • moduleAction A M (x := op x) (y := y) h
      (f.v k (s + k) (by omega) t) (by omega) := by
  change (evaluation _ _).f n
    ((uncurryRight (𝟙 (homComplex A K (M.obj (op x)))) ⊗ₘ M.map (op x) y).f n
      ((α_ (homComplex A K (M.obj (op x))) K (op x ⟶[Complex A] y)).inv.f n
        (ιTensorObj (homComplex A K (M.obj (op x))) (K ⊗ (op x ⟶[Complex A] y))
          s r n (by omega) (f ⊗ₜ[A] ιTensorObj K (op x ⟶[Complex A] y)
            k q r hr (t ⊗ₜ[A] h))))) = _
  rw [associator_inv_apply, tensorMap_apply, evaluation_apply, uncurryRight_apply]
  rfl

/-- 中間の M(x) 次数を指定した自由 Hom 拡張の公式。 -/
lemma freeExtensionApp_apply_of_sum (x : D) (K : Complex A) (M : RightModule A D)
    (y : Dᵒᵖ) (s k q r b n : ℤ) (hr : k + q = r) (hb : k + s = b) (hn : r + s = n)
    (f : Homogeneous K (M.obj (op x)) s) (t : K.X k)
    (h : GradedHom A y.unop x q) :
    ((freeExtensionApp A x K M y).f s f).v r n hn
      (ιTensorObj K (y.unop ⟶[Complex A] x) k q r hr (t ⊗ₜ[A] h)) =
    (b * q).negOnePow • moduleAction A M (x := op x) (y := y) h
      (f.v k b hb t) (by omega) := by
  have hb0 : b = s + k := by omega
  cases hb0
  exact freeExtensionApp_apply A x K M y s k q r n hr hn f t h

/-- 自由 Hom 拡張は全次数の豊穣自然性を持つ。 -/
lemma freeExtensionApp_naturality (x : D) (K : Complex A) (M : RightModule A D)
    (y z : Dᵒᵖ) :
    (β_ (homComplex A K (M.obj (op x))) (y ⟶[Complex A] z)).hom ≫
      ((freeModule x K).map y z ⊗ₘ freeExtensionApp A x K M z) ≫
        enrichedComposition _ _ _ =
      (freeExtensionApp A x K M y ⊗ₘ M.map y z) ≫ enrichedComposition _ _ _ := by
  apply moduleParamNaturality_of_cochain A
    (M := freeModule x K) (N := M) (freeExtensionApp A x K M)
  intro y z s p m hm ψ g
  apply Cochain.ext
  intro r n hn
  apply mapBifunctor.hom_ext
  intro i q hr
  change i + q = r at hr
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro t h
  rw [Cochain.comp_v _ _ (by omega) r (r + p) n rfl (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ hm r (r + s) n rfl (by omega)]
  change ((freeExtensionApp A x K M z).f s ψ).v (r + p) n (by omega)
    (moduleAction A (freeModule x K) g
      (ιTensorObj K (y.unop ⟶[Complex A] x) i q r hr (t ⊗ₜ[A] h)) rfl) =
    (s * p).negOnePow • moduleAction A M g
      (((freeExtensionApp A x K M y).f s ψ).v r (r + s) rfl
        (ιTensorObj K (y.unop ⟶[Complex A] x) i q r hr (t ⊗ₜ[A] h))) (by omega)
  rw [tensorModule_action K (representable A x) y z p i q r (q + p) (r + p)
    hr rfl rfl]
  simp only [Units.smul_def, map_zsmul]
  rw [freeExtensionApp_apply, freeExtensionApp_apply]
  have he := moduleAction_representable A x M y z p q (s + i) (q + p) n (r + s)
    rfl (by omega) (by omega) g h (ψ.v i (s + i) (by omega) t)
  rw [he]
  unfold moduleAction
  simp only [Units.smul_def, map_zsmul, smul_smul]
  change ((p * i).negOnePow * ((s + i) * (q + p)).negOnePow) • (_ : (M.obj z).X n) =
    ((s * p).negOnePow * ((s + i) * q).negOnePow) • (_ : (M.obj z).X n)
  rw [← Int.negOnePow_add, ← Int.negOnePow_add]
  have hd : p * i + (s + i) * (q + p) = s * p + (s + i) * q + 2 * (p * i) := by ring
  rw [hd, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

/-- 全次数 Hom(K,M(x)) を自由加群からの豊穣自然変換として拡張する。 -/
def freeExtension (x : D) (K : Complex A) (M : RightModule A D) :
    ModuleParamTrans A D (homComplex A K (M.obj (op x))) (freeModule x K) M where
  app := freeExtensionApp A x K M
  naturality := freeExtensionApp_naturality A x K M

/-- 全次数自然な成分族を代表の単位で評価する chain map。 -/
def freeFamilyEvaluation (x : D) (K : Complex A) (M : RightModule A D) {E : Complex A}
    (σ : ∀ y : Dᵒᵖ, E ⟶ homComplex A ((freeModule x K).obj y) (M.obj y)) :
    E ⟶ homComplex A K (M.obj (op x)) :=
  σ (op x) ≫ homPrecompose (freeUnitInsert A x K) (M.obj (op x))

/-- 成分族の自由評価の斉次公式。 -/
lemma freeFamilyEvaluation_apply (x : D) (K : Complex A) (M : RightModule A D) {E : Complex A}
    (σ : ∀ y : Dᵒᵖ, E ⟶ homComplex A ((freeModule x K).obj y) (M.obj y))
    (s k n : ℤ) (hn : k + s = n) (f : E.X s) (t : K.X k) :
    ((freeFamilyEvaluation A x K M σ).f s f).v k n hn t =
    ((σ (op x)).f s f).v k n hn
      (ιTensorObj K (x ⟶[Complex A] x) k 0 k (add_zero k)
        (t ⊗ₜ[A] (unitElement A x).val)) := by
  change ((Cochain.ofHom (freeUnitInsert A x K)).comp
    ((σ (op x)).f s f) (zero_add s)).v k n hn t = _
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  change ((σ (op x)).f s f).v k n hn ((freeUnitInsert A x K).f k t) = _
  rw [freeUnitInsert_apply]

/-- 自由 Hom 拡張は単位での評価により元の斉次 Hom に戻る。 -/
lemma freeFamilyEvaluation_extension (x : D) (K : Complex A) (M : RightModule A D) :
    freeFamilyEvaluation A x K M (freeExtensionApp A x K M) =
      𝟙 (homComplex A K (M.obj (op x))) := by
  apply HomologicalComplex.Hom.ext
  funext s
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  apply Cochain.ext
  intro k n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  rw [freeFamilyEvaluation_apply,
    freeExtensionApp_apply_of_sum A x K M (op x) s k 0 k n n
      (add_zero k) hn hn]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact moduleAction_unit A M (op x) n (ψ.v k n hn t)

/-- 全次数自然な自由 Hom 成分族は単位での評価から復元できる。 -/
lemma freeFamilyEvaluation_restore (x : D) (K : Complex A) (M : RightModule A D)
    {E : Complex A}
    (σ : ∀ y : Dᵒᵖ, E ⟶ homComplex A ((freeModule x K).obj y) (M.obj y))
    (hσ : ∀ y z : Dᵒᵖ, (β_ E (y ⟶[Complex A] z)).hom ≫
      ((freeModule x K).map y z ⊗ₘ σ z) ≫ enrichedComposition _ _ _ =
        (σ y ⊗ₘ M.map y z) ≫ enrichedComposition _ _ _) (y : Dᵒᵖ) :
    freeFamilyEvaluation A x K M σ ≫ freeExtensionApp A x K M y = σ y := by
  apply HomologicalComplex.Hom.ext
  funext s
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  apply Cochain.ext
  intro r n hn
  apply mapBifunctor.hom_ext
  intro k q hr
  change k + q = r at hr
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro t h
  change ((freeExtensionApp A x K M y).f s
      ((freeFamilyEvaluation A x K M σ).f s ψ)).v r n hn
      (ιTensorObj K (y.unop ⟶[Complex A] x) k q r hr (t ⊗ₜ[A] h)) =
    ((σ y).f s ψ).v r n hn
      (ιTensorObj K (y.unop ⟶[Complex A] x) k q r hr (t ⊗ₜ[A] h))
  rw [freeExtensionApp_apply_of_sum A x K M y s k q r (k + s) n hr rfl hn,
    freeFamilyEvaluation_apply]
  have he := moduleParamNaturality_apply_of_sum A σ hσ (x := op x) (y := y)
    (k := s) (p := q) (r := k) (m := s + q) (n := n) (s := r) (l := k + s)
    ψ h (ιTensorObj K (x ⟶[Complex A] x) k 0 k (add_zero k)
      (t ⊗ₜ[A] (unitElement A x).val)) rfl (by omega) (by omega) rfl
  rw [tensorModule_action K (representable A x) (op x) y q k 0 k q r
    (add_zero k) (zero_add q) (by omega)] at he
  have hu : moduleAction A (representable A x) (x := op x) (y := y) h
      (unitElement A x).val (zero_add q) = h := by
    change forward A (x := y.unop) (y := x) (z := x) h (unitElement A x).val
      (add_zero q) = h
    exact unit_forward A h
  rw [hu] at he
  simp only [Units.smul_def, map_zsmul] at he
  change (q * k).negOnePow • ((σ y).f s ψ).v r n hn
      (ιTensorObj K (y.unop ⟶[Complex A] x) k q r hr (t ⊗ₜ[A] h)) =
    (s * q).negOnePow • moduleAction A M h
      (((σ (op x)).f s ψ).v k (k + s) rfl
        (ιTensorObj K (x ⟶[Complex A] x) k 0 k (add_zero k)
          (t ⊗ₜ[A] (unitElement A x).val))) (by omega) at he
  have he' := congrArg (fun z => (q * k).negOnePow • z) he
  rw [smul_smul, Int.units_mul_self, one_smul, smul_smul, ← Int.negOnePow_add] at he'
  have hd : q * k + s * q = (k + s) * q := by ring
  rw [hd] at he'
  exact he'.symm

variable (D) [Small.{u} D]
/-- Hom end の全次数の自由生成元での評価。 -/
def freeHomEvaluation (x : D) (K : Complex A) (M : RightModule A D) :
    moduleHom A D (freeModule x K) M ⟶ homComplex A K (M.obj (op x)) :=
  moduleHomπ A D (freeModule x K) M x ≫ homPrecompose (freeUnitInsert A x K) (M.obj (op x))

/-- end の自由評価の斉次公式。 -/
lemma freeHomEvaluation_apply (x : D) (K : Complex A) (M : RightModule A D)
    (s k n : ℤ) (hn : k + s = n) (f : (moduleHom A D (freeModule x K) M).X s)
    (t : K.X k) :
    ((freeHomEvaluation A D x K M).f s f).v k n hn t =
    ((moduleHomπ A D (freeModule x K) M x).f s f).v k n hn
      (ιTensorObj K (x ⟶[Complex A] x) k 0 k (add_zero k)
        (t ⊗ₜ[A] (unitElement A x).val)) := by
  change ((Cochain.ofHom (freeUnitInsert A x K)).comp
    ((moduleHomπ A D (freeModule x K) M x).f s f) (zero_add s)).v k n hn t = _
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  change ((moduleHomπ A D (freeModule x K) M x).f s f).v k n hn
    ((freeUnitInsert A x K).f k t) = _
  rw [freeUnitInsert_apply]
/-- 全次数の自由拡張を主 Hom end に持ち上げる。 -/
def freeHomExtension (x : D) (K : Complex A) (M : RightModule A D) :
    homComplex A K (M.obj (op x)) ⟶ moduleHom A D (freeModule x K) M :=
  (moduleHomEquiv A D _ (freeModule x K) M).symm (freeExtension A x K M)

/-- 全次数の自由拡張の end 成分。 -/
@[reassoc (attr := simp)]
lemma freeHomExtension_π (x : D) (K : Complex A) (M : RightModule A D) (y : D) :
    freeHomExtension A D x K M ≫ moduleHomπ A D (freeModule x K) M y =
      freeExtensionApp A x K M (op y) :=
  moduleHomEquiv_symm_π A D _ _ _ _ _
/-- 自由加群の全次数 Hom end は通常の線形 Hom 複体と chain iso。 -/
def freeHomIso (x : D) (K : Complex A) (M : RightModule A D) :
    moduleHom A D (freeModule x K) M ≅ homComplex A K (M.obj (op x)) where
  hom := freeHomEvaluation A D x K M
  inv := freeHomExtension A D x K M
  hom_inv_id := by
    apply moduleHom_ext
    intro y
    rw [Category.assoc, freeHomExtension_π]
    change freeFamilyEvaluation A x K M
      (fun y => moduleHomπ A D (freeModule x K) M y.unop) ≫
        freeExtensionApp A x K M (op y) = 𝟙 _ ≫ moduleHomπ A D (freeModule x K) M y
    simpa only [Category.id_comp] using freeFamilyEvaluation_restore A x K M
      (fun y => moduleHomπ A D (freeModule x K) M y.unop)
      (moduleHomπ_naturality A D (freeModule x K) M) (op y)
  inv_hom_id := by
    rw [freeHomEvaluation, ← Category.assoc, freeHomExtension_π]
    exact freeFamilyEvaluation_extension A x K M
end SerrePositivity.DifferentialGraded
