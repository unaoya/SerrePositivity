module

public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.Basic

/-!
# Module.TensorFree

## 概要
5 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## TensorShift（旧 SerrePositivity/DifferentialGraded/Module/TensorShift.lean） -/

/-! # tensor因子のshiftとdg加群shiftの比較 -/

@[expose] public section TensorShift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左因子をshiftしたtensor加群と、tensor加群のshiftの全dg自然な同型。 -/
def tensorModuleShiftIso (K : Complex A) (M : RightModule A D) (s : ℤ) :
    ForgetEnrichment.of (Complex A) (tensorModule (K⟦s⟧) M) ≅
      (ForgetEnrichment.of (Complex A) (tensorModule K M))⟦s⟧ :=
  moduleIsoMk A D (M := tensorModule (K⟦s⟧) M) (N := shiftModule s (tensorModule K M))
    (fun x => SerrePositivity.cochainTensorShiftLeft K (M.obj x) s) (by
      intro x y
      change (M.map x y ≫ tensorLeftHom (K⟦s⟧) (M.obj x) (M.obj y)) ≫
        homPostcompose _ (SerrePositivity.cochainTensorShiftLeft K (M.obj y) s).hom = _
      simp only [Category.assoc]
      rw [tensorShiftLeft_hom_naturality]
      rfl)

@[simp] lemma tensorModuleShiftIso_hom_eval (K : Complex A) (M : RightModule A D)
    (s : ℤ) (x : D) :
    (moduleEvaluation A D x).map (tensorModuleShiftIso A D K M s).hom =
      (SerrePositivity.cochainTensorShiftLeft K (M.obj (op x)) s).hom :=
  moduleIsoMk_hom_eval A D _ _ x

@[simp] lemma tensorModuleShiftIso_inv_eval (K : Complex A) (M : RightModule A D)
    (s : ℤ) (x : D) :
    (moduleEvaluation A D x).map (tensorModuleShiftIso A D K M s).inv =
      (SerrePositivity.cochainTensorShiftLeft K (M.obj (op x)) s).inv :=
  moduleIsoMk_inv_eval A D _ _ x

/-- free_xは複体の整数shiftを加群shiftへ運ぶ。 -/
def freeAtShiftIso (x : D) (K : Complex A) (s : ℤ) :
    (freeAt x).obj (K⟦s⟧) ≅ ((freeAt x).obj K)⟦s⟧ :=
  tensorModuleShiftIso A D K (representable A x) s

end SerrePositivity.DifferentialGraded
end

end TensorShift

/-! ## TensorAdjunction（旧 SerrePositivity/DifferentialGraded/Module/TensorAdjunction.lean） -/

/-! # tensor した右 dg 加群の閉射の転置 -/

@[expose] public section TensorAdjunction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end TensorAdjunction

/-! ## TensorUnit（旧 SerrePositivity/DifferentialGraded/Module/TensorUnit.lean） -/

/-! # tensor 加群の左単位とパラメータ射の逆転置 -/

@[expose] public section TensorUnit
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end TensorUnit

/-! ## FreeHom（旧 SerrePositivity/DifferentialGraded/Module/FreeHom.lean） -/

/-! # 自由加群の全次数 Hom 複体 -/

@[expose] public section FreeHom
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end FreeHom

/-! ## FreeHomNaturality（旧 SerrePositivity/DifferentialGraded/Module/FreeHomNaturality.lean） -/

/-! # 自由加群の全次数 Hom 同型の自然性 -/

@[expose] public section FreeHomNaturality
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 自由 Hom 複体同型は値域の加群射に対して自然。 -/
lemma freeHomIso_naturality_target (x : D) (K : Complex A) {M N : ModuleCategory A D}
    (f : M ⟶ N) :
    eHomWhiskerLeft (Complex A) ((freeAt x).obj K) f ≫
      (freeHomIso A D x K (ForgetEnrichment.to (Complex A) N)).hom =
    (freeHomIso A D x K (ForgetEnrichment.to (Complex A) M)).hom ≫
      homPostcompose K ((moduleEvaluation A D x).map f) := by
  have hp := moduleHomWhiskerLeft_π A D (M := (freeAt x).obj K) f x
  have ht := congrArg (fun q :
      moduleHom A D (freeModule x K) (ForgetEnrichment.to (Complex A) M) ⟶
        homComplex A (K ⊗ (x ⟶[Complex A] x)) ((ForgetEnrichment.to (Complex A) N).obj (op x)) =>
    q ≫ homPrecompose (freeUnitInsert A x K) ((ForgetEnrichment.to (Complex A) N).obj (op x))) hp
  calc
    _ = (eHomWhiskerLeft (Complex A) ((freeAt x).obj K) f ≫
        moduleHomπ A D (freeModule x K) (ForgetEnrichment.to (Complex A) N) x) ≫
        homPrecompose (freeUnitInsert A x K) ((ForgetEnrichment.to (Complex A) N).obj (op x)) :=
      (Category.assoc _ _ _).symm
    _ = (moduleHomπ A D (freeModule x K) (ForgetEnrichment.to (Complex A) M) x ≫
        homPostcompose (K ⊗ (x ⟶[Complex A] x)) ((moduleEvaluation A D x).map f)) ≫
        homPrecompose (freeUnitInsert A x K) ((ForgetEnrichment.to (Complex A) N).obj (op x)) := ht
    _ = _ := by
      have hc := homPostcompose_precompose A (freeUnitInsert A x K)
        ((moduleEvaluation A D x).map f)
      have he := congrArg (fun q :
          homComplex A (K ⊗ (x ⟶[Complex A] x)) ((ForgetEnrichment.to (Complex A) M).obj (op x)) ⟶
            homComplex A K ((ForgetEnrichment.to (Complex A) N).obj (op x)) =>
        moduleHomπ A D (freeModule x K) (ForgetEnrichment.to (Complex A) M) x ≫ q) hc
      exact (Category.assoc _ _ _).trans (he.trans (Category.assoc _ _ _).symm)

omit [Small.{u} D] in
/-- 自由生成元の単位挿入は生成する複体の chain map に対して自然。 -/
lemma freeUnitInsert_naturality (x : D) {K L : Complex A} (g : L ⟶ K) :
    freeUnitInsert A x L ≫ (g ⊗ₘ 𝟙 (x ⟶[Complex A] x)) = g ≫ freeUnitInsert A x K := by
  dsimp only [freeUnitInsert]
  rw [Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.id_comp, Category.comp_id]
  rw [rightUnitor_inv_comp_tensorHom]
  simp only [id_tensorHom]

/-- 自由 Hom 複体同型は生成する複体の chain map に対して反変に自然。 -/
lemma freeHomIso_naturality_source (x : D) {K L : Complex A} (g : L ⟶ K)
    (M : ModuleCategory A D) :
    eHomWhiskerRight (Complex A) ((freeAt x).map g) M ≫
      (freeHomIso A D x L (ForgetEnrichment.to (Complex A) M)).hom =
    (freeHomIso A D x K (ForgetEnrichment.to (Complex A) M)).hom ≫
      homPrecompose g ((moduleEvaluation A D x).obj M) := by
  have hp := moduleHomWhiskerRight_π A D ((freeAt x).map g) (P := M) x
  have ht := congrArg (fun q :
      moduleHom A D (freeModule x K) (ForgetEnrichment.to (Complex A) M) ⟶
        homComplex A (L ⊗ (x ⟶[Complex A] x)) ((ForgetEnrichment.to (Complex A) M).obj (op x)) =>
    q ≫ homPrecompose (freeUnitInsert A x L) ((ForgetEnrichment.to (Complex A) M).obj (op x))) hp
  have hg : (moduleEvaluation A D x).map ((freeAt x).map g) =
      g ⊗ₘ 𝟙 (x ⟶[Complex A] x) := tensorModuleMap_eval g (representable A x) x
  have hi : freeUnitInsert A x L ≫ (moduleEvaluation A D x).map ((freeAt x).map g) =
      g ≫ freeUnitInsert A x K := by
    rw [hg]
    exact freeUnitInsert_naturality A D x g
  calc
    _ = (eHomWhiskerRight (Complex A) ((freeAt x).map g) M ≫
        moduleHomπ A D (freeModule x L) (ForgetEnrichment.to (Complex A) M) x) ≫
        homPrecompose (freeUnitInsert A x L) ((ForgetEnrichment.to (Complex A) M).obj (op x)) :=
      (Category.assoc _ _ _).symm
    _ = (moduleHomπ A D (freeModule x K) (ForgetEnrichment.to (Complex A) M) x ≫
        homPrecompose ((moduleEvaluation A D x).map ((freeAt x).map g))
          ((ForgetEnrichment.to (Complex A) M).obj (op x))) ≫
        homPrecompose (freeUnitInsert A x L) ((ForgetEnrichment.to (Complex A) M).obj (op x)) := ht
    _ = _ := by
      rw [Category.assoc, ← homPrecompose_comp, hi, homPrecompose_comp]
      rfl
/-- 全次数 Hom 複体同型の閉零制限は通常の自由評価随伴の Hom 同値と一致する。 -/
lemma freeHomIso_closed_zero (x : D) (K : Complex A) (M : ModuleCategory A D)
    (f : (freeAt x).obj K ⟶ M) :
    mapFromUnit A K ((ForgetEnrichment.to (Complex A) M).obj (op x))
      (ForgetEnrichment.homTo (Complex A) (C := RightModule A D)
          (X := (freeAt x).obj K) (Y := M) f ≫
        (freeHomIso A D x K (ForgetEnrichment.to (Complex A) M)).hom) =
      freeHomEquiv A D x K M f := by
  apply Cochain.ofHom_injective
  rw [mapFromUnit_cochain, cycleFromUnit_postcomp]
  apply Cochain.ext₀
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change ((freeHomEvaluation A D x K (ForgetEnrichment.to (Complex A) M)).f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (C := RightModule A D) f)).val).v
      k k (add_zero k) t = _
  rw [freeHomEvaluation_apply]
  have he := moduleEvaluation_cochain A D x f
  have hv := congrArg (fun z : Homogeneous (K ⊗ (x ⟶[Complex A] x))
      ((ForgetEnrichment.to (Complex A) M).obj (op x)) 0 =>
    z.v k k (add_zero k)
      (ιTensorObj K (x ⟶[Complex A] x) k 0 k (add_zero k)
        (t ⊗ₜ[A] (unitElement A x).val))) he
  calc
    _ = ((moduleEvaluation A D x).map f).f k
        (ιTensorObj K (x ⟶[Complex A] x) k 0 k (add_zero k)
          (t ⊗ₜ[A] (unitElement A x).val)) := hv.symm
    _ = (Cochain.ofHom (freeHomEquiv A D x K M f)).v k k (add_zero k) t := by
      rw [Cochain.ofHom_v, freeHomEquiv_apply]
end SerrePositivity.DifferentialGraded
end

end FreeHomNaturality
