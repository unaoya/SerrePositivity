module

public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.HomologicalAlgebra.TensorBaseChangeNaturality
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import SerrePositivity.HomologicalAlgebra.CochainTensor.BaseChange
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

public import SerrePositivity.DifferentialGraded.Module.Basic

public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Tensor.ScalarExtension.CategoriesAndModules

## 概要
dg 圏・加群・全 Hom の係数変更と制限比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## RestrictionComparison（旧 SerrePositivity/DifferentialGraded/Tensor/RestrictionComparison.lean） -/

/-! # dg関手に沿うbalanced tensorの比較chain map

## 概要
制限した二因子のtensorから元のtensorへの写像を普遍性で構成する。
準同型性はここでは仮定・主張せず、導来合成比較に使う実際の写像を固定する。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 両作用を制限したtensorから元のtensorへの比較chain map。 -/
def restrictionComparison (M : RightModule A E) (N : LeftModule A E) :
    obj A D (restrictModule A D E F.op M) (F.comp N) ⟶ obj A E M N :=
  desc A D _ _ (restrictFamily A D E F M N
    (homEquiv A E M N _ (𝟙 (obj A E M N))))

@[reassoc (attr := simp)]
lemma ι_restrictionComparison (M : RightModule A E) (N : LeftModule A E) (x : D) :
    ι A D (restrictModule A D E F.op M) (F.comp N) x ≫
        restrictionComparison A D E F M N = ι A E M N (F.obj x) := by
  rw [restrictionComparison, ι_desc]
  exact Category.comp_id _

/-- 比較chain mapは各純粋斉次tensorを同じ元の像へ送る。追加の符号は生じない。 -/
lemma restrictionComparison_element (M : RightModule A E) (N : LeftModule A E) (x : D)
    {r s n : ℤ} (m : (M.obj (op (F.obj x))).X r) (t : (N.obj (F.obj x)).X s)
    (hn : r + s = n) :
    (restrictionComparison A D E F M N).f n
        (element A D (restrictModule A D E F.op M) (F.comp N) x m t hn) =
      element A E M N (F.obj x) m t hn :=
  congrArg (fun k => k.f n
    (ιTensorObj (M.obj (op (F.obj x))) (N.obj (F.obj x)) r s n hn (m ⊗ₜ[A] t)))
      (ι_restrictionComparison A D E F M N x)

/-- 任意のbalanced族への比較は、族の引き戻しと一致する。 -/
lemma restrictionComparison_desc (M : RightModule A E) (N : LeftModule A E)
    {T : Complex A} (a : BalancedFamily A E M N T) :
    restrictionComparison A D E F M N ≫ desc A E M N a =
      desc A D _ _ (restrictFamily A D E F M N a) := by
  apply hom_ext
  intro x
  rw [ι_restrictionComparison_assoc, ι_desc, ι_desc]
  rfl

omit [Small.{u} D] [Small.{u} E] in
lemma rightAction_restrict_family {M M' : RightModule A E}
    (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x))
    (hf : ∀ x y, rightAction A E M x y ≫ f x =
      (f y ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫ rightAction A E M' x y) (x y : D) :
    rightAction A D (restrictModule A D E F.op M) x y ≫ f (F.obj x) =
      (f (F.obj y) ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫
        rightAction A D (restrictModule A D E F.op M') x y := by
  rw [rightAction_restrict, rightAction_restrict, Category.assoc, hf]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

omit [Small.{u} D] [Small.{u} E] in
lemma leftAction_restrict_family {N N' : LeftModule A E}
    (g : ∀ x, N.obj x ⟶ N'.obj x)
    (hg : ∀ x y, leftAction A E N x y ≫ g y =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ g x) ≫ leftAction A E N' x y) (x y : D) :
    leftAction A D (F.comp N) x y ≫ g (F.obj y) =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ g (F.obj x)) ≫ leftAction A D (F.comp N') x y := by
  rw [leftAction_restrict, leftAction_restrict, Category.assoc, hg]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

/-- 比較chain mapは作用と可換な任意の二つのchain map族に関して自然。 -/
lemma restrictionComparison_naturality {M M' : RightModule A E} {N N' : LeftModule A E}
    (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x)) (g : ∀ x, N.obj x ⟶ N'.obj x)
    (hf : ∀ x y, rightAction A E M x y ≫ f x =
      (f y ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫ rightAction A E M' x y)
    (hg : ∀ x y, leftAction A E N x y ≫ g y =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ g x) ≫ leftAction A E N' x y) :
    mapOfFamilies A D (fun x => f (F.obj x)) (fun x => g (F.obj x))
        (rightAction_restrict_family A D E F f hf) (leftAction_restrict_family A D E F g hg) ≫
      restrictionComparison A D E F M' N' =
    restrictionComparison A D E F M N ≫ mapOfFamilies A E f g hf hg := by
  apply hom_ext
  intro x
  simp only [ι_mapOfFamilies_assoc, ι_restrictionComparison,
    ι_restrictionComparison_assoc, ι_mapOfFamilies]

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end RestrictionComparison

/-! ## RestrictionComparisonCoherence（旧 SerrePositivity/DifferentialGraded/Tensor/RestrictionComparisonCoherence.lean） -/

/-! # 制限tensor比較のdg関手合成に関する整合性

## 概要
制限tensor比較のdg関手合成に関する整合性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionComparisonCoherence
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] (T : Type z) [DGCategory A T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

lemma rightAction_restrict_comp (M : RightModule A T) (x y : D) :
    rightAction A D (restrictModule A D E F.op (restrictModule A E T G.op M)) x y =
      rightAction A D (restrictModule A D T (F.comp G).op M) x y := by
  change (signedSwap _ _).hom ≫ uncurryRight
    (F.map x y ≫ (G.map (F.obj x) (F.obj y) ≫ M.map _ _)) =
      (signedSwap _ _).hom ≫ uncurryRight
        ((F.map x y ≫ G.map (F.obj x) (F.obj y)) ≫ M.map _ _)
  rw [Category.assoc]

lemma leftAction_restrict_comp (N : LeftModule A T) (x y : D) :
    leftAction A D (F.comp (G.comp N)) x y = leftAction A D ((F.comp G).comp N) x y := by
  change uncurryRight (F.map x y ≫ (G.map (F.obj x) (F.obj y) ≫ N.map _ _)) =
    uncurryRight ((F.map x y ≫ G.map (F.obj x) (F.obj y)) ≫ N.map _ _)
  rw [Category.assoc]

variable [Small.{u} D]

/-- 反復制限と合成制限のtensorを恒等成分で比較する。 -/
def restrictionComparisonCompIso (M : RightModule A T) (N : LeftModule A T) :
    obj A D (restrictModule A D E F.op (restrictModule A E T G.op M)) (F.comp (G.comp N)) ≅
      obj A D (restrictModule A D T (F.comp G).op M) ((F.comp G).comp N) where
  hom := mapOfFamilies A D (fun _ => 𝟙 _) (fun _ => 𝟙 _)
    (fun x y => by
      simpa only [tensorHom_id, id_whiskerRight, Category.comp_id, Category.id_comp] using
        rightAction_restrict_comp A D E T F G M x y)
    (fun x y => by
      simpa only [tensorHom_id, id_whiskerRight, Category.comp_id, Category.id_comp] using
        leftAction_restrict_comp A D E T F G N x y)
  inv := mapOfFamilies A D (fun _ => 𝟙 _) (fun _ => 𝟙 _)
    (fun x y => by
      simpa only [tensorHom_id, id_whiskerRight, Category.comp_id, Category.id_comp] using
        (rightAction_restrict_comp A D E T F G M x y).symm)
    (fun x y => by
      simpa only [tensorHom_id, id_whiskerRight, Category.comp_id, Category.id_comp] using
        (leftAction_restrict_comp A D E T F G N x y).symm)
  hom_inv_id := by
    apply hom_ext
    intro x
    simp only [ι_mapOfFamilies_assoc, ι_mapOfFamilies, tensorHom_id, id_whiskerRight,
      Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply hom_ext
    intro x
    simp only [ι_mapOfFamilies_assoc, ι_mapOfFamilies, tensorHom_id, id_whiskerRight,
      Category.id_comp, Category.comp_id]

@[reassoc (attr := simp)]
lemma ι_restrictionComparisonCompIso_hom (M : RightModule A T) (N : LeftModule A T) (x : D) :
    ι A D (restrictModule A D E F.op (restrictModule A E T G.op M)) (F.comp (G.comp N)) x ≫
        (restrictionComparisonCompIso A D E T F G M N).hom =
      ι A D (restrictModule A D T (F.comp G).op M) ((F.comp G).comp N) x := by
  dsimp only [restrictionComparisonCompIso]
  simp only [ι_mapOfFamilies, tensorHom_id, id_whiskerRight, Category.id_comp]

@[reassoc (attr := simp)]
lemma ι_restrictionComparisonCompIso_inv (M : RightModule A T) (N : LeftModule A T) (x : D) :
    ι A D (restrictModule A D T (F.comp G).op M) ((F.comp G).comp N) x ≫
        (restrictionComparisonCompIso A D E T F G M N).inv =
      ι A D (restrictModule A D E F.op (restrictModule A E T G.op M)) (F.comp (G.comp N)) x := by
  dsimp only [restrictionComparisonCompIso]
  simp only [ι_mapOfFamilies, tensorHom_id, id_whiskerRight, Category.id_comp]

variable [Small.{u} E] [Small.{u} T]

/-- 二段階での比較chain mapは合成関手による一段階の比較と可換。 -/
lemma restrictionComparison_comp (M : RightModule A T) (N : LeftModule A T) :
    (restrictionComparisonCompIso A D E T F G M N).hom ≫
        restrictionComparison A D T (F.comp G) M N =
      restrictionComparison A D E F (restrictModule A E T G.op M) (G.comp N) ≫
        restrictionComparison A E T G M N := by
  apply hom_ext
  intro x
  rw [ι_restrictionComparisonCompIso_hom_assoc, ι_restrictionComparison,
    ι_restrictionComparison_assoc, ι_restrictionComparison]
  rfl

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end RestrictionComparisonCoherence

/-! ## ScalarExtensionColimits（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionColimits.lean） -/

/-! # 非有界複体の係数変更と余極限

任意の環準同型に対する underived な比較。係数環の平坦性は要求しない。
擬同型の保存はこのファイルの余極限保存からは結論しない。
-/

@[expose] public section ScalarExtensionColimits
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- 各次数で A' ⊗_A − を施す。 -/
abbrev extension : Complex A ⥤ Complex A' :=
  (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)

/-- 微分を変えずに各次数で係数を制限する。 -/
abbrev restriction : Complex A' ⥤ Complex A :=
  (ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)

/-- 加群の随伴を非有界複体に持ち上げる。 -/
def adjunction : extension φ ⊣ restriction φ :=
  Adjunction.mkOfUnitCounit {
    unit := (ModuleCat.extendRestrictScalarsAdj φ).unit.mapHomologicalComplex (.up ℤ)
    counit := (ModuleCat.extendRestrictScalarsAdj φ).counit.mapHomologicalComplex (.up ℤ)
    left_triangle := by
      apply NatTrans.ext
      funext K
      apply HomologicalComplex.hom_ext
      intro n
      simp
    right_triangle := by
      apply NatTrans.ext
      funext K
      apply HomologicalComplex.hom_ext
      intro n
      simp }

instance : (extension φ).IsLeftAdjoint := (adjunction φ).isLeftAdjoint
instance : (restriction φ).IsRightAdjoint := (adjunction φ).isRightAdjoint

/-- 直和の比較は同じ添字集合を使う。 -/
def coproductIso {I : Type v} [Small.{u} I] (K : I → Complex A) :
    (extension φ).obj (∐ K) ≅ ∐ (fun i => (extension φ).obj (K i)) :=
  PreservesCoproduct.iso (extension φ) K

@[reassoc (attr := simp)]
lemma map_ι_coproductIso {I : Type v} [Small.{u} I] (K : I → Complex A) (i : I) :
    (extension φ).map (Sigma.ι K i) ≫ (coproductIso φ K).hom =
      Sigma.ι (fun i => (extension φ).obj (K i)) i := by
  apply (cancel_mono (coproductIso φ K).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (ι_comp_sigmaComparison (extension φ) K i).symm

/-- coequalizer も平坦性なしで係数拡大と可換する。 -/
def coequalizerIso {K L : Complex A} (f g : K ⟶ L) :
    (extension φ).obj (coequalizer f g) ≅
      coequalizer ((extension φ).map f) ((extension φ).map g) :=
  (PreservesCoequalizer.iso (extension φ) f g).symm

@[reassoc (attr := simp)]
lemma map_π_coequalizerIso {K L : Complex A} (f g : K ⟶ L) :
    (extension φ).map (coequalizer.π f g) ≫ (coequalizerIso φ f g).hom =
      coequalizer.π ((extension φ).map f) ((extension φ).map g) :=
  map_π_preserves_coequalizer_inv (extension φ) f g

/-- 二つの非有界複体の total tensor との比較。 -/
abbrev tensorIso (K L : Complex A) :
    (extension φ).obj (K ⊗ L) ≅ (extension φ).obj K ⊗ (extension φ).obj L :=
  cochainTensorBaseChangeIso φ K L

@[reassoc]
lemma tensorIso_naturality {K K' L L' : Complex A} (f : K ⟶ K') (g : L ⟶ L') :
    (extension φ).map (f ⊗ₘ g) ≫ (tensorIso φ K' L').hom =
      (tensorIso φ K L).hom ≫ ((extension φ).map f ⊗ₘ (extension φ).map g) :=
  cochainTensorBaseChangeIso_naturality φ f g

/-- 恒等係数変更との比較。 -/
def identityIso : extension (RingHom.id A) ≅ 𝟭 (Complex A) :=
  NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId A) (.up ℤ)

/-- 連続した二回の係数変更との比較。 -/
def compositionIso {A'' : Type u} [CommRing A''] (ψ : A' →+* A'') :
    extension φ ⋙ extension ψ ≅ extension (ψ.comp φ) :=
  Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp φ ψ).symm (.up ℤ)

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionColimits

/-! ## ScalarExtensionCoherence（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionCoherence.lean） -/

/-! # 係数変更の tensor 比較の整合性 -/

@[expose] public section ScalarExtensionCoherence
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types true
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- 任意の整数次数に置いた係数環の係数変更。 -/
def sphereIso (n : ℤ) :
    (extension φ).obj (complexSphere A n) ≅ complexSphere A' n :=
  (singleMapHomologicalComplex (ModuleCat.extendScalars φ) (.up ℤ) n).app _ ≪≫
    (single (ModuleCat A') (.up ℤ) n).mapIso
      (Functor.Monoidal.εIso (ModuleCat.extendScalars φ)).symm

/-- 単位複体との比較。 -/
abbrev unitIso : (extension φ).obj (𝟙_ (Complex A)) ≅ 𝟙_ (Complex A') := sphereIso φ 0

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma sphereIso_one (n : ℤ) :
    let := φ.toAlgebra
    (sphereIso φ n).hom.f n
      ((1 : A') ⊗ₜ[A] (singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv (1 : A)) =
        (singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A'))).inv (1 : A') := by
  let := φ.toAlgebra
  simp only [sphereIso, Iso.trans_hom, comp_f]
  erw [single_map_f_self]
  simp only [Functor.mapHomologicalComplex_obj_X, Functor.comp_obj, Iso.app_hom,
    singleMapHomologicalComplex_hom_app_self, Iso.symm_hom, Functor.Monoidal.εIso_inv,
    Category.assoc, Iso.inv_hom_id_assoc, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, ModuleCat.ExtendScalars.map_tmul, Iso.inv_hom_id_apply]
  rw [ModuleCat.extendScalars_η]
  erw [TensorProduct.AlgebraTensorModule.rid_tmul (R := A) (A := A') (M := A') (1 : A) (1 : A')]
  simp

set_option maxHeartbeats 800000 in
-- 各次数での係数変更と total tensor の型の展開に必要。
lemma tensorIso_left_unitor (K : Complex A) :
    (λ_ ((extension φ).obj K)).inv = (extension φ).map (λ_ K).inv ≫
      (tensorIso φ (𝟙_ (Complex A)) K).hom ≫ (unitIso φ).hom ▷ (extension φ).obj K := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro n
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (λ_ ((extension φ).obj K)).inv.f n ((1 : A') ⊗ₜ[A] x) =
    (cochainTensorMap (unitIso φ).hom (𝟙 _)).f n
      ((tensorIso φ (𝟙_ (Complex A)) K).hom.f n
        ((ModuleCat.extendScalars φ).map ((λ_ K).inv.f n) ((1 : A') ⊗ₜ[A] x)))
  erw [ModuleCat.ExtendScalars.map_tmul φ]
  simp only [complexLeftUnitor_inv_apply]
  dsimp only [tensorIso]
  erw [cochainTensorBaseChangeIso_apply_ι φ (𝟙_ (Complex A)) K 0 n n (zero_add n)
    ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) x]
  erw [cochainTensorMap_apply_ι (unitIso φ).hom (𝟙 ((extension φ).obj K))]
  erw [sphereIso_one φ]
  convert complexLeftUnitor_inv_apply ((extension φ).obj K) n ((1 : A') ⊗ₜ[A] x) using 1; rfl

set_option maxHeartbeats 800000 in
-- 各次数での係数変更と total tensor の型の展開に必要。
lemma tensorIso_right_unitor (K : Complex A) :
    (ρ_ ((extension φ).obj K)).inv = (extension φ).map (ρ_ K).inv ≫
      (tensorIso φ K (𝟙_ (Complex A))).hom ≫ (extension φ).obj K ◁ (unitIso φ).hom := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro n
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (ρ_ ((extension φ).obj K)).inv.f n ((1 : A') ⊗ₜ[A] x) =
    (cochainTensorMap (𝟙 _) (unitIso φ).hom).f n
      ((tensorIso φ K (𝟙_ (Complex A))).hom.f n
        ((ModuleCat.extendScalars φ).map ((ρ_ K).inv.f n) ((1 : A') ⊗ₜ[A] x)))
  erw [ModuleCat.ExtendScalars.map_tmul φ]
  simp only [complexRightUnitor_inv_apply]
  dsimp only [tensorIso]
  erw [cochainTensorBaseChangeIso_apply_ι φ K (𝟙_ (Complex A)) n 0 n (add_zero n)
    x ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))]
  erw [cochainTensorMap_apply_ι (𝟙 ((extension φ).obj K)) (unitIso φ).hom]
  erw [sphereIso_one φ]
  convert complexRightUnitor_inv_apply ((extension φ).obj K) n ((1 : A') ⊗ₜ[A] x) using 1; rfl

set_option maxHeartbeats 1600000 in
-- 三重 total tensor の成分を展開して比較する。
@[reassoc]
lemma tensorIso_associator (K L M : Complex A) :
    (tensorIso φ (K ⊗ L) M).hom ≫ (tensorIso φ K L).hom ▷ (extension φ).obj M ≫
        (α_ ((extension φ).obj K) ((extension φ).obj L) ((extension φ).obj M)).hom =
      (extension φ).map (α_ K L M).hom ≫ (tensorIso φ K (L ⊗ M)).hom ≫
        (extension φ).obj K ◁ (tensorIso φ L M).hom := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro n
  apply cochainTensorTripleBaseChange_hom_ext φ K L M n
  intro i j k h
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change (cochainTensorAssociator _ _ _).hom.f n
    ((cochainTensorMap (tensorIso φ K L).hom (𝟙 _)).f n
      ((tensorIso φ (K ⊗ L) M).hom.f n
        ((1 : A') ⊗ₜ[A] cochainTensorTripleι K L M i j k n h ((x ⊗ₜ[A] y) ⊗ₜ[A] z)))) =
    (cochainTensorMap (𝟙 _) (tensorIso φ L M).hom).f n
      ((tensorIso φ K (L ⊗ M)).hom.f n
        ((ModuleCat.extendScalars φ).map ((cochainTensorAssociator K L M).hom.f n)
          ((1 : A') ⊗ₜ[A] cochainTensorTripleι K L M i j k n h ((x ⊗ₜ[A] y) ⊗ₜ[A] z))))
  dsimp only [tensorIso]
  erw [cochainTensorTripleι_apply]
  erw [cochainTensorBaseChangeIso_apply_ι φ (K ⊗ L) M (i + j) k n h
    (ιTensorObj K L i j (i + j) rfl (x ⊗ₜ[A] y)) z]
  erw [cochainTensorMap_apply_ι]
  erw [cochainTensorBaseChangeIso_apply_ι φ K L i j (i + j) rfl x y]
  erw [cochainTensorAssociator_hom_apply_ι]
  erw [ModuleCat.ExtendScalars.map_tmul φ, cochainTensorAssociator_hom_apply_ι]
  erw [cochainTensorBaseChangeIso_apply_ι φ K (L ⊗ M) i (j + k) n (by omega)
    x (ιTensorObj L M j k (j + k) rfl (y ⊗ₜ[A] z))]
  erw [cochainTensorMap_apply_ι]
  erw [cochainTensorBaseChangeIso_apply_ι φ L M j k (j + k) rfl y z]
  rfl

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionCoherence

/-! ## ScalarExtension（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtension.lean） -/

/-! # dg 圏の underived 係数変更

同じ対象に、係数拡大した Hom を置く。Mathlib の豊穣構造の移送を使う。
-/

@[expose] public section ScalarExtension
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory Limits MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- 非有界複体の係数拡大は強モノイダル。平坦性を仮定しない。 -/
instance extensionMonoidal : (extension φ).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    (Functor.CoreMonoidal.mk'
      (εIso := (unitIso φ).symm)
      (μIso := fun K L => (tensorIso φ K L).symm)
      (μIso_inv_natural_left := fun f L => by
        simpa using (tensorIso_naturality φ f (𝟙 L)).symm)
      (μIso_inv_natural_right := fun K f => by
        simpa using (tensorIso_naturality φ (𝟙 K) f).symm)
      (oplax_associativity := tensorIso_associator φ)
      (oplax_left_unitality := tensorIso_left_unitor φ)
      (oplax_right_unitality := tensorIso_right_unitor φ))

/-- 対象は D のまま、Hom を係数拡大する Mathlib の型別名。 -/
abbrev DGBaseChange (D : Type v) [DGCategory A D] := TransportEnrichment (extension φ) D

variable (D : Type v) [DGCategory A D]

lemma homObject_eq (x y : DGBaseChange φ D) :
    homObject A' (DGBaseChange φ D) x y = (extension φ).obj (homObject A D x y) := rfl

lemma identity_eq (x : DGBaseChange φ D) :
    eId (Complex A') x = (unitIso φ).inv ≫ (extension φ).map (eId (Complex A) (C := D) x) := rfl

lemma composition_eq (x y z : DGBaseChange φ D) :
    eComp (Complex A') x y z = (tensorIso φ (homObject A D x y) (homObject A D y z)).inv ≫
      (extension φ).map (eComp (Complex A) (C := D) x y z) := rfl

variable {D} {E : Type w} [DGCategory A E]

/-- dg 関手にも Hom ごとに係数拡大を施す。 -/
def dgFunctor (F : DGFunctor A D E) :
    DGFunctor A' (DGBaseChange φ D) (DGBaseChange φ E) where
  obj := F.obj
  map x y := (extension φ).map (F.map x y)
  map_id x := by
    change (unitIso φ).inv ≫ (extension φ).map (eId (Complex A) (C := D) x) ≫
      (extension φ).map (F.map x x) = _
    rw [← Functor.map_comp, F.map_id]
    rfl
  map_comp x y z := by
    change (tensorIso φ _ _).inv ≫ (extension φ).map (eComp (Complex A) (C := D) x y z) ≫
      (extension φ).map (F.map x z) = _
    rw [← Functor.map_comp, F.map_comp, Functor.map_comp]
    change Functor.LaxMonoidal.μ (extension φ) _ _ ≫
      (extension φ).map (F.map x y ⊗ₘ F.map y z) ≫ _ = _
    rw [← Functor.LaxMonoidal.μ_natural_assoc]
    rfl

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtension

/-! ## ScalarExtensionHom（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionHom.lean） -/

/-! # 係数変更と全次数 Hom の比較

全次数 Hom の係数変更から、係数変更した複体間の Hom への射。
これが同型であるという有限性条件は仮定しない。
-/

@[expose] public section ScalarExtensionHom
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- 評価の係数変更を転置した全次数 Hom 比較。 -/
def homComparison (K L : Complex A) :
    (extension φ).obj (homComplex A K L) ⟶
      homComplex A' ((extension φ).obj K) ((extension φ).obj L) :=
  curryRight ((tensorIso φ (homComplex A K L) K).inv ≫
    (extension φ).map (uncurryRight (𝟙 (homComplex A K L))))

set_option maxHeartbeats 800000 in
-- total tensor の同型の逆を純粋生成元上で計算する。
lemma tensorIso_inv_apply (K L : Complex A) (i j n : ℤ) (h : i + j = n)
    (x : K.X i) (y : L.X j) :
    let := φ.toAlgebra
    (tensorIso φ K L).inv.f n
      (ιTensorObj ((extension φ).obj K) ((extension φ).obj L) i j n h
        (((1 : A') ⊗ₜ[A] x) ⊗ₜ[A'] ((1 : A') ⊗ₜ[A] y))) =
      (1 : A') ⊗ₜ[A] ιTensorObj K L i j n h (x ⊗ₜ[A] y) := by
  let := φ.toAlgebra
  have he := cochainTensorBaseChangeIso_apply_ι φ K L i j n h x y
  have hi := congrArg (fun z => (tensorIso φ K L).inv.f n z) he
  have hc := congrArg (fun f => f.f n
    ((1 : A') ⊗ₜ[A] ιTensorObj K L i j n h (x ⊗ₜ[A] y))) (tensorIso φ K L).hom_inv_id
  exact hi.symm.trans hc

set_option maxHeartbeats 800000 in
-- 係数制限の加群表示を展開して純粋生成元上で評価する。
lemma homComparison_apply (K L : Complex A) (p i n : ℤ) (h : i + p = n)
    (f : Homogeneous K L p) (x : K.X i) :
    let := φ.toAlgebra
    ((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f)).v i n h
      ((1 : A') ⊗ₜ[A] x) = (1 : A') ⊗ₜ[A] f.v i n h x := by
  let := φ.toAlgebra
  change ((extension φ).map (uncurryRight (𝟙 (homComplex A K L)))).f n
    ((tensorIso φ (homComplex A K L) K).inv.f n
      (ιTensorObj ((extension φ).obj (homComplex A K L)) ((extension φ).obj K) p i n (by omega)
        (((1 : A') ⊗ₜ[A] f) ⊗ₜ[A'] ((1 : A') ⊗ₜ[A] x)))) = _
  erw [tensorIso_inv_apply φ (homComplex A K L) K p i n (by omega) f x]
  erw [ModuleCat.ExtendScalars.map_tmul φ, uncurryRight_apply]
  rfl

lemma sphereIso_inv_one (n : ℤ) :
    let := φ.toAlgebra
    (sphereIso φ n).inv.f n
      ((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A'))).inv (1 : A')) =
        (1 : A') ⊗ₜ[A] (singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv (1 : A) := by
  let := φ.toAlgebra
  have hi := congrArg (fun z => (sphereIso φ n).inv.f n z) (sphereIso_one φ n)
  have hc := congrArg (fun f => f.f n
    ((1 : A') ⊗ₜ[A] (singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv (1 : A)))
    (sphereIso φ n).hom_inv_id
  exact hi.symm.trans hc

set_option maxHeartbeats 800000 in
-- Hom 比較の全次数成分を評価して単位を照合する。
lemma homComparison_identity (K : Complex A) :
    (unitIso φ).inv ≫ (extension φ).map (identity K) ≫ homComparison φ K K =
      identity ((extension φ).obj K) := by
  let := φ.toAlgebra
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (homComparison φ K K).f 0
    ((ModuleCat.extendScalars φ).map ((identity K).f 0)
      ((unitIso φ).inv.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A'))).inv (1 : A')))) = _
  erw [sphereIso_inv_one φ 0, ModuleCat.ExtendScalars.map_tmul φ]
  have hid : (identity K).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) = Cochain.ofHom (𝟙 K) := by
    exact congrArg Subtype.val (cycleFromUnit_unitFromCycle _ _)
  rw [hid]
  change (homComparison φ K K).f 0 ((1 : A') ⊗ₜ[A] Cochain.ofHom (𝟙 K)) =
    (cycleFromUnit _ (identity ((extension φ).obj K))).val
  rw [identity, cycleFromUnit_unitFromCycle]
  apply Cochain.ext₀
  intro i
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((homComparison φ K K).f 0 ((1 : A') ⊗ₜ[A] Cochain.ofHom (𝟙 K))).v i i (add_zero i)
    ((1 : A') ⊗ₜ[A] x) = (1 : A') ⊗ₜ[A] x
  erw [homComparison_apply φ K K 0 i i (add_zero i)]
  rfl

set_option maxHeartbeats 1600000 in
-- 二つの斉次 Hom と値の純粋生成元上で合成を比較する。
lemma homComparison_composition (K L M : Complex A) :
    (tensorIso φ (homComplex A K L) (homComplex A L M)).inv ≫
        (extension φ).map (enrichedComposition K L M) ≫ homComparison φ K M =
      (homComparison φ K L ⊗ₘ homComparison φ L M) ≫
        enrichedComposition ((extension φ).obj K) ((extension φ).obj L) ((extension φ).obj M) := by
  let := φ.toAlgebra
  apply (cancel_epi (tensorIso φ (homComplex A K L) (homComplex A L M)).hom).1
  rw [Iso.hom_inv_id_assoc]
  apply HomologicalComplex.hom_ext
  intro n
  apply cochainTensorBaseChange_hom_ext φ (homComplex A K L) (homComplex A L M)
  intro p q hpq
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change (homComparison φ K M).f n
    ((ModuleCat.extendScalars φ).map ((enrichedComposition K L M).f n)
      ((1 : A') ⊗ₜ[A] ιTensorObj (homComplex A K L) (homComplex A L M) p q n hpq
        (f ⊗ₜ[A] g))) =
    (enrichedComposition _ _ _).f n
      ((homComparison φ K L ⊗ₘ homComparison φ L M).f n
        ((tensorIso φ (homComplex A K L) (homComplex A L M)).hom.f n
          ((1 : A') ⊗ₜ[A] ιTensorObj (homComplex A K L) (homComplex A L M) p q n hpq
            (f ⊗ₜ[A] g))))
  erw [ModuleCat.ExtendScalars.map_tmul φ, enrichedComposition_apply]
  erw [cochainTensorBaseChangeIso_apply_ι φ (homComplex A K L) (homComplex A L M)]
  erw [tensorMap_apply, enrichedComposition_apply]
  apply Cochain.ext
  intro i j hij
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((homComparison φ K M).f n ((1 : A') ⊗ₜ[A] ((p * q).negOnePow • f.comp g hpq))).v
    i j hij ((1 : A') ⊗ₜ[A] x) =
      ((p * q).negOnePow •
        ((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f)).comp
          ((homComparison φ L M).f q ((1 : A') ⊗ₜ[A] g)) hpq).v i j hij ((1 : A') ⊗ₜ[A] x)
  erw [homComparison_apply φ K M n i j hij]
  rw [Cochain.units_smul_v, Cochain.units_smul_v]
  rw [Cochain.comp_v f g hpq i (i + p) j rfl (by omega),
    Cochain.comp_v _ _ hpq i (i + p) j rfl (by omega)]
  change (1 : A') ⊗ₜ[A] ((p * q).negOnePow •
    g.v (i + p) j (by omega) (f.v i (i + p) rfl x)) =
      (p * q).negOnePow •
        ((homComparison φ L M).f q ((1 : A') ⊗ₜ[A] g)).v (i + p) j (by omega)
          (((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f)).v i (i + p) rfl ((1 : A') ⊗ₜ[A] x))
  erw [homComparison_apply φ K L p i (i + p) rfl,
    homComparison_apply φ L M q (i + p) j (by omega)]
  simp only [Units.smul_def, TensorProduct.tmul_smul]
  rfl

/-- 複体の係数変更を、移送した自己豊穣構造からの dg 関手として読む。 -/
def complexDGFunctor : DGFunctor A' (DGBaseChange φ (Complex A)) (Complex A') where
  obj := (extension φ).obj
  map K L := homComparison φ K L
  map_id K := homComparison_identity φ K
  map_comp K L M := homComparison_composition φ K L M

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionHom

/-! ## ScalarExtensionModule（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionModule.lean） -/

/-! # dg 加群の対象の係数変更 -/

@[expose] public section ScalarExtensionModule
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

@[reassoc]
lemma tensorIso_braiding (K L : Complex A) :
    (β_ ((extension φ).obj K) ((extension φ).obj L)).hom ≫ (tensorIso φ L K).inv =
      (tensorIso φ K L).inv ≫ (extension φ).map (β_ K L).hom := by
  apply (cancel_epi (tensorIso φ K L).hom).1
  rw [Iso.hom_inv_id_assoc]
  have h := congrArg (fun f => f ≫ (tensorIso φ L K).inv)
    (cochainTensorBaseChangeIso_symmetry φ K L)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  convert h.symm using 1

variable (D : Type v) [DGCategory A D]

/-- 係数変更と opposite を交換する恒等 Hom の dg 関手。
合成の符号は強モノイダル構造の braiding 整合性から得る。 -/
def oppositeDGFunctor :
    DGFunctor A' (DGBaseChange φ D)ᵒᵖ (DGBaseChange φ Dᵒᵖ) where
  obj x := op (show D from x.unop)
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp x y z := by
    change ((β_ _ _).hom ≫ (tensorIso φ _ _).inv ≫
      (extension φ).map (eComp (Complex A) (C := D) z.unop y.unop x.unop)) ≫ 𝟙 _ =
        (𝟙 _ ⊗ₘ 𝟙 _) ≫ (tensorIso φ _ _).inv ≫
          (extension φ).map ((β_ _ _).hom ≫
            eComp (Complex A) (C := D) z.unop y.unop x.unop)
    simp only [Category.comp_id, tensorHom_id, Functor.map_comp]
    rw [tensorIso_braiding_assoc]
    simp only [id_whiskerRight, Category.id_comp]

/-- 各値を係数拡大した右 dg 加群。作用は全次数 Hom 比較を通して定義する。 -/
def rightModule (M : RightModule A D) : RightModule A' (DGBaseChange φ D) :=
  ((oppositeDGFunctor φ D).comp (dgFunctor φ M.toFunctor)).comp (complexDGFunctor φ)

/-- 左 dg 加群の係数変更。 -/
def leftModule (M : LeftModule A D) : LeftModule A' (DGBaseChange φ D) :=
  (dgFunctor φ M).comp (complexDGFunctor φ)

lemma rightModule_obj (M : RightModule A D) (x : D) :
    (rightModule φ D M).obj (op x) = (extension φ).obj (M.obj (op x)) := rfl

lemma leftModule_obj (M : LeftModule A D) (x : D) :
    (leftModule φ D M).obj x = (extension φ).obj (M.obj x) := rfl

set_option backward.isDefEq.respectTransparency true in
lemma rightModule_action (M : RightModule A D) (x y : Dᵒᵖ) (p r n : ℤ)
    (h : r + p = n) (f : GradedHom A x y p) (m : (M.obj x).X r) :
    let := φ.toAlgebra
    moduleAction A' (rightModule φ D M) (x := x) (y := y)
      ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] m) h =
        (1 : A') ⊗ₜ[A] moduleAction A M f m h := by
  let := φ.toAlgebra
  change ((homComparison φ (M.obj x) (M.obj y)).f p
    ((ModuleCat.extendScalars φ).map ((M.map x y).f p)
      ((𝟙 ((extension φ).obj (x ⟶[Complex A] y)) :
        (extension φ).obj (x ⟶[Complex A] y) ⟶ (extension φ).obj (x ⟶[Complex A] y)).f p
          ((1 : A') ⊗ₜ[A] f)))).v r n h
        ((1 : A') ⊗ₜ[A] m) = _
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  erw [ModuleCat.ExtendScalars.map_tmul φ,
    homComparison_apply φ (M.obj x) (M.obj y) p r n h]
  rfl

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionModule

/-! ## ScalarExtensionCochain（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionCochain.lean） -/

/-! # 係数変更と閉性を仮定しない斉次 cochain

path の ε 消去には次数 +1 の cochain が必要なため、chain map に限定しない。
-/

@[expose] public section ScalarExtensionCochain
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- 各斉次成分での係数変更の可換四角形。 -/
def CochainSquare {P Q : Complex A} {P' Q' : Complex A'} {p : ℤ}
    (a : (extension φ).obj P ⟶ P') (b : (extension φ).obj Q ⟶ Q')
    (f : Cochain P Q p) (g : Cochain P' Q' p) : Prop :=
  ∀ i j (h : i + p = j), (ModuleCat.extendScalars φ).map (f.v i j h) ≫ b.f j =
    a.f i ≫ g.v i j h

lemma cochainSquare_ofHom {P Q : Complex A} {P' Q' : Complex A'}
    (a : (extension φ).obj P ⟶ P') (b : (extension φ).obj Q ⟶ Q')
    (f : P ⟶ Q) (g : P' ⟶ Q') (h : (extension φ).map f ≫ b = a ≫ g) :
    CochainSquare φ a b (Cochain.ofHom f) (Cochain.ofHom g) := by
  intro i j hij
  have hj : j = i := by omega
  cases hj
  rw [Cochain.ofHom_v, Cochain.ofHom_v]
  convert congrArg (fun z => z.f i) h using 1 <;> rfl

lemma cochainSquare_comp {P Q R : Complex A} {P' Q' R' : Complex A'}
    {a : (extension φ).obj P ⟶ P'} {b : (extension φ).obj Q ⟶ Q'}
    {c : (extension φ).obj R ⟶ R'} {p q n : ℤ}
    {f : Cochain P Q p} {g : Cochain Q R q} {f' : Cochain P' Q' p} {g' : Cochain Q' R' q}
    (hf : CochainSquare φ a b f f') (hg : CochainSquare φ b c g g') (hn : p + q = n) :
    CochainSquare φ a c (f.comp g hn) (f'.comp g' hn) := by
  intro i j hij
  rw [Cochain.comp_v f g hn i (i + p) j rfl (by omega),
    Cochain.comp_v f' g' hn i (i + p) j rfl (by omega),
    CategoryTheory.Functor.map_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

set_option maxHeartbeats 800000 in
-- 係数拡大した二重 tensor の全次数生成元で Koszul 符号を照合する。
lemma cochainSquare_tensorLeft {K P Q : Complex A} {K' P' Q' : Complex A'}
    (k : (extension φ).obj K ⟶ K')
    {a : (extension φ).obj P ⟶ P'} {b : (extension φ).obj Q ⟶ Q'} {p : ℤ}
    {f : Cochain P Q p} {g : Cochain P' Q' p} (hf : CochainSquare φ a b f g) :
    CochainSquare φ ((tensorIso φ K P).hom ≫ (k ⊗ₘ a))
      ((tensorIso φ K Q).hom ≫ (k ⊗ₘ b))
      ((tensorLeftHom K P Q).f p f) ((tensorLeftHom K' P' Q').f p g) := by
  let := φ.toAlgebra
  intro s n hsn
  apply cochainTensorBaseChange_hom_ext φ K P
  intro i j hij
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (k ⊗ₘ b).f n ((tensorIso φ K Q).hom.f n
    ((ModuleCat.extendScalars φ).map (((tensorLeftHom K P Q).f p f).v s n hsn)
      ((1 : A') ⊗ₜ[A] ιTensorObj K P i j s hij (x ⊗ₜ[A] y)))) =
    ((tensorLeftHom K' P' Q').f p g).v s n hsn
      ((k ⊗ₘ a).f s ((tensorIso φ K P).hom.f s
        ((1 : A') ⊗ₜ[A] ιTensorObj K P i j s hij (x ⊗ₜ[A] y))))
  erw [ModuleCat.ExtendScalars.map_tmul φ, tensorLeftHom_apply]
  simp only [Units.smul_def, TensorProduct.tmul_smul, map_zsmul]
  erw [cochainTensorBaseChangeIso_apply_ι φ K Q i (j + p) n (by omega)]
  erw [cochainTensorBaseChangeIso_apply_ι φ K P i j s hij]
  erw [tensorMap_apply, tensorMap_apply, tensorLeftHom_apply]
  have hh := congrArg (fun z => z ((1 : A') ⊗ₜ[A] y)) (hf j (j + p) rfl)
  change b.f (j + p) ((1 : A') ⊗ₜ[A] f.v j (j + p) rfl y) =
    g.v j (j + p) rfl (a.f j ((1 : A') ⊗ₜ[A] y)) at hh
  rw [hh]
  rfl

set_option maxHeartbeats 800000 in
-- 右 tensor には追加の符号がなく、同じ純粋生成元で照合できる。
lemma cochainSquare_tensorRight {K P Q : Complex A} {K' P' Q' : Complex A'}
    (k : (extension φ).obj K ⟶ K')
    {a : (extension φ).obj P ⟶ P'} {b : (extension φ).obj Q ⟶ Q'} {p : ℤ}
    {f : Cochain P Q p} {g : Cochain P' Q' p} (hf : CochainSquare φ a b f g) :
    CochainSquare φ ((tensorIso φ P K).hom ≫ (a ⊗ₘ k))
      ((tensorIso φ Q K).hom ≫ (b ⊗ₘ k))
      ((tensorRightHom K P Q).f p f) ((tensorRightHom K' P' Q').f p g) := by
  let := φ.toAlgebra
  intro s n hsn
  apply cochainTensorBaseChange_hom_ext φ P K
  intro i j hij
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (b ⊗ₘ k).f n ((tensorIso φ Q K).hom.f n
    ((ModuleCat.extendScalars φ).map (((tensorRightHom K P Q).f p f).v s n hsn)
      ((1 : A') ⊗ₜ[A] ιTensorObj P K i j s hij (x ⊗ₜ[A] y)))) =
    ((tensorRightHom K' P' Q').f p g).v s n hsn
      ((a ⊗ₘ k).f s ((tensorIso φ P K).hom.f s
        ((1 : A') ⊗ₜ[A] ιTensorObj P K i j s hij (x ⊗ₜ[A] y))))
  erw [ModuleCat.ExtendScalars.map_tmul φ, tensorRightHom_apply]
  erw [cochainTensorBaseChangeIso_apply_ι φ Q K (i + p) j n (by omega)]
  erw [cochainTensorBaseChangeIso_apply_ι φ P K i j s hij]
  erw [tensorMap_apply, tensorMap_apply, tensorRightHom_apply]
  have hh := congrArg (fun z => z ((1 : A') ⊗ₜ[A] x)) (hf i (i + p) rfl)
  change b.f (i + p) ((1 : A') ⊗ₜ[A] f.v i (i + p) rfl x) =
    g.v i (i + p) rfl (a.f i ((1 : A') ⊗ₜ[A] x)) at hh
  rw [hh]

lemma cochainSquare_zero {P Q : Complex A} {P' Q' : Complex A'} {p : ℤ}
    (a : (extension φ).obj P ⟶ P') (b : (extension φ).obj Q ⟶ Q') :
    CochainSquare φ a b (0 : Cochain P Q p) 0 := by
  intro i j h
  simp only [Cochain.zero_v, Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

lemma cochainSquare_add {P Q : Complex A} {P' Q' : Complex A'} {p : ℤ}
    {a : (extension φ).obj P ⟶ P'} {b : (extension φ).obj Q ⟶ Q'}
    {f g : Cochain P Q p} {f' g' : Cochain P' Q' p}
    (hf : CochainSquare φ a b f f') (hg : CochainSquare φ a b g g') :
    CochainSquare φ a b (f + g) (f' + g') := by
  intro i j h
  simp only [Cochain.add_v, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
    hf i j h, hg i j h]

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionCochain

/-! ## ScalarExtensionDiagrams（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionDiagrams.lean） -/

/-! # tensor 式の係数変更を組み立てる比較射 -/

@[expose] public section ScalarExtensionDiagrams
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

def compareTensor {P Q : Complex A} {P' Q' : Complex A'}
    (a : (extension φ).obj P ⟶ P') (b : (extension φ).obj Q ⟶ Q') :
    (extension φ).obj (P ⊗ Q) ⟶ P' ⊗ Q' :=
  (tensorIso φ P Q).hom ≫ (a ⊗ₘ b)

lemma compareTensor_naturality {P Q R T : Complex A} {P' Q' R' T' : Complex A'}
    {a : (extension φ).obj P ⟶ P'} {b : (extension φ).obj Q ⟶ Q'}
    {c : (extension φ).obj R ⟶ R'} {d : (extension φ).obj T ⟶ T'}
    (f : P ⟶ R) (g : Q ⟶ T) (f' : P' ⟶ R') (g' : Q' ⟶ T')
    (hf : (extension φ).map f ≫ c = a ≫ f')
    (hg : (extension φ).map g ≫ d = b ≫ g') :
    (extension φ).map (f ⊗ₘ g) ≫ compareTensor φ c d =
      compareTensor φ a b ≫ (f' ⊗ₘ g') := by
  unfold compareTensor
  rw [← Category.assoc, tensorIso_naturality, Category.assoc,
    tensorHom_comp_tensorHom, hf, hg, ← tensorHom_comp_tensorHom, Category.assoc]

lemma compareTensor_associator {P Q R : Complex A} {P' Q' R' : Complex A'}
    (a : (extension φ).obj P ⟶ P') (b : (extension φ).obj Q ⟶ Q')
    (c : (extension φ).obj R ⟶ R') :
    (extension φ).map (α_ P Q R).hom ≫ compareTensor φ a (compareTensor φ b c) =
      compareTensor φ (compareTensor φ a b) c ≫ (α_ P' Q' R').hom := by
  have hl : a ⊗ₘ ((tensorIso φ Q R).hom ≫ (b ⊗ₘ c)) =
      ((extension φ).obj P ◁ (tensorIso φ Q R).hom) ≫ (a ⊗ₘ (b ⊗ₘ c)) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  have hr : ((tensorIso φ P Q).hom ≫ (a ⊗ₘ b)) ⊗ₘ c =
      ((tensorIso φ P Q).hom ▷ (extension φ).obj R) ≫ ((a ⊗ₘ b) ⊗ₘ c) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  unfold compareTensor
  rw [hl, hr]
  simp only [Category.assoc]
  rw [← tensorIso_associator_assoc]
  rw [← associator_naturality]

lemma compareTensor_associator_inv {P Q R : Complex A} {P' Q' R' : Complex A'}
    (a : (extension φ).obj P ⟶ P') (b : (extension φ).obj Q ⟶ Q')
    (c : (extension φ).obj R ⟶ R') :
    (extension φ).map (α_ P Q R).inv ≫ compareTensor φ (compareTensor φ a b) c =
      compareTensor φ a (compareTensor φ b c) ≫ (α_ P' Q' R').inv := by
  have h := congrArg (fun f => (extension φ).map (α_ P Q R).inv ≫ f ≫ (α_ P' Q' R').inv)
    (compareTensor_associator φ a b c)
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

lemma compareTensor_leftUnitor {P : Complex A} {P' : Complex A'}
    (a : (extension φ).obj P ⟶ P') :
    (extension φ).map (λ_ P).hom ≫ a =
      compareTensor φ (unitIso φ).hom a ≫ (λ_ P').hom := by
  have h := Functor.Monoidal.map_leftUnitor (extension φ) P
  change (extension φ).map (λ_ P).hom =
    (tensorIso φ (𝟙_ (Complex A)) P).hom ≫
      (unitIso φ).hom ▷ (extension φ).obj P ≫ (λ_ ((extension φ).obj P)).hom at h
  rw [h]
  unfold compareTensor
  rw [← tensorHom_id, Category.assoc, Category.assoc, ← leftUnitor_naturality,
    ← id_tensorHom, tensorHom_comp_tensorHom_assoc]
  simp only [Category.comp_id, Category.id_comp, Category.assoc]

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionDiagrams

/-! ## ScalarExtensionNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionNaturality.lean） -/

/-! # 全次数 Hom の係数変更比較の両変数自然性 -/

@[expose] public section ScalarExtensionNaturality
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

@[reassoc]
lemma homComparison_postcompose (K : Complex A) {L L' : Complex A} (g : L ⟶ L') :
    (extension φ).map (homPostcompose K g) ≫ homComparison φ K L' =
      homComparison φ K L ≫ homPostcompose ((extension φ).obj K) ((extension φ).map g) := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro p
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (homComparison φ K L').f p
    ((ModuleCat.extendScalars φ).map ((homPostcompose K g).f p) ((1 : A') ⊗ₜ[A] f)) =
      (homPostcompose ((extension φ).obj K) ((extension φ).map g)).f p
        ((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f))
  erw [ModuleCat.ExtendScalars.map_tmul φ, homPostcompose_apply, homPostcompose_apply]
  apply Cochain.ext
  intro i n h
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((homComparison φ K L').f p
    ((1 : A') ⊗ₜ[A] f.comp (Cochain.ofHom g) (add_zero p))).v i n h ((1 : A') ⊗ₜ[A] x) =
      (((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f)).comp
        (Cochain.ofHom ((extension φ).map g)) (add_zero p)).v i n h ((1 : A') ⊗ₜ[A] x)
  erw [homComparison_apply φ K L' p i n h]
  rw [Cochain.comp_zero_cochain_v, Cochain.comp_zero_cochain_v]
  change (1 : A') ⊗ₜ[A] g.f n (f.v i n h x) =
    (ModuleCat.extendScalars φ).map (g.f n)
      (((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f)).v i n h ((1 : A') ⊗ₜ[A] x))
  erw [homComparison_apply φ K L p i n h, ModuleCat.ExtendScalars.map_tmul φ]

@[reassoc]
lemma homComparison_precompose {K K' : Complex A} (f : K' ⟶ K) (L : Complex A) :
    (extension φ).map (homPrecompose f L) ≫ homComparison φ K' L =
      homComparison φ K L ≫ homPrecompose ((extension φ).map f) ((extension φ).obj L) := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro p
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change (homComparison φ K' L).f p
    ((ModuleCat.extendScalars φ).map ((homPrecompose f L).f p) ((1 : A') ⊗ₜ[A] g)) =
      (homPrecompose ((extension φ).map f) ((extension φ).obj L)).f p
        ((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] g))
  erw [ModuleCat.ExtendScalars.map_tmul φ, homPrecompose_apply, homPrecompose_apply]
  apply Cochain.ext
  intro i n h
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((homComparison φ K' L).f p
    ((1 : A') ⊗ₜ[A] (Cochain.ofHom f).comp g (zero_add p))).v i n h ((1 : A') ⊗ₜ[A] x) =
      ((Cochain.ofHom ((extension φ).map f)).comp
        ((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] g)) (zero_add p)).v i n h ((1 : A') ⊗ₜ[A] x)
  erw [homComparison_apply φ K' L p i n h]
  rw [Cochain.zero_cochain_comp_v, Cochain.zero_cochain_comp_v]
  change (1 : A') ⊗ₜ[A] g.v i n h (f.f i x) =
    ((homComparison φ K L).f p ((1 : A') ⊗ₜ[A] g)).v i n h
      ((ModuleCat.extendScalars φ).map (f.f i) ((1 : A') ⊗ₜ[A] x))
  erw [ModuleCat.ExtendScalars.map_tmul φ, homComparison_apply φ K L p i n h]

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionNaturality

/-! ## ScalarExtensionModuleMaps（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionModuleMaps.lean） -/

/-! # dg 加群圏上の係数拡大関手 -/

@[expose] public section ScalarExtensionModuleMaps
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

instance smallDGBaseChange [Small.{u} D] : Small.{u} (DGBaseChange φ D) :=
  inferInstanceAs (Small.{u} D)

lemma rightModule_map (M : RightModule A D) (x y : (DGBaseChange φ D)ᵒᵖ) :
    (rightModule φ D M).map x y =
      (extension φ).map (M.map x y) ≫ homComparison φ (M.obj x) (M.obj y) := by
  change (𝟙 _ ≫ (extension φ).map (M.map x y)) ≫ _ = _
  rw [Category.id_comp]
  rfl

lemma rightModule_family_naturality {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : (DGBaseChange φ D)ᵒᵖ) :
    (rightModule φ D M).map x y ≫
        homPostcompose ((rightModule φ D M).obj x) ((extension φ).map (a y)) =
      (rightModule φ D N).map x y ≫
        homPrecompose ((extension φ).map (a x)) ((rightModule φ D N).obj y) := by
  rw [rightModule_map, rightModule_map, Category.assoc]
  change (extension φ).map (M.map x y) ≫ homComparison φ (M.obj x) (M.obj y) ≫
      homPostcompose ((extension φ).obj (M.obj x)) ((extension φ).map (a y)) =
    ((extension φ).map (N.map x y) ≫ homComparison φ (N.obj x) (N.obj y)) ≫
      homPrecompose ((extension φ).map (a x)) ((extension φ).obj (N.obj y))
  erw [← homComparison_postcompose φ (M.obj x) (a y)]
  rw [← CategoryTheory.Functor.map_comp_assoc, h, CategoryTheory.Functor.map_comp, Category.assoc]
  erw [homComparison_precompose φ (a x) (N.obj y)]
  exact (Category.assoc _ _ _).symm

variable [Small.{u} D]

/-- 全次数自然な射の各値を係数拡大し、実際の加群圏の射へ戻す。 -/
def moduleExtensionMap {M N : ModuleCategory A D} (f : M ⟶ N) :
    ForgetEnrichment.of (Complex A') (rightModule φ D (ForgetEnrichment.to (Complex A) M)) ⟶
      ForgetEnrichment.of (Complex A') (rightModule φ D (ForgetEnrichment.to (Complex A) N)) :=
  moduleMorphismMk A' (DGBaseChange φ D)
    (fun x => (extension φ).map ((moduleEvaluation A D x.unop).map f))
    (rightModule_family_naturality φ D
      (closedTransApp A (moduleClosedHomEquiv A D M N f))
      (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f)))

@[simp]
lemma moduleExtensionMap_eval {M N : ModuleCategory A D} (f : M ⟶ N)
    (x : DGBaseChange φ D) :
    (moduleEvaluation A' (DGBaseChange φ D) x).map (moduleExtensionMap φ D f) =
      (extension φ).map ((moduleEvaluation A D (show D from x)).map f) :=
  moduleMorphismMk_eval A' (DGBaseChange φ D) _ _ x

/-- 係数拡大は加群の対象と全次数自然な射の両方に定義される。 -/
def moduleExtension : ModuleCategory A D ⥤ ModuleCategory A' (DGBaseChange φ D) where
  obj M := ForgetEnrichment.of (Complex A')
    (rightModule φ D (ForgetEnrichment.to (Complex A) M))
  map f := moduleExtensionMap φ D f
  map_id M := by
    apply moduleMorphism_ext
    intro x
    rw [moduleExtensionMap_eval, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply moduleMorphism_ext
    intro x
    rw [moduleExtensionMap_eval, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      moduleExtensionMap_eval, moduleExtensionMap_eval]

@[simp]
lemma moduleExtension_eval {M N : ModuleCategory A D} (f : M ⟶ N)
    (x : DGBaseChange φ D) :
    (moduleEvaluation A' (DGBaseChange φ D) x).map ((moduleExtension φ D).map f) =
      (extension φ).map ((moduleEvaluation A D (show D from x)).map f) :=
  moduleExtensionMap_eval φ D f x

def moduleExtensionEvaluationIso (x : DGBaseChange φ D) :
    moduleExtension φ D ⋙ moduleEvaluation A' (DGBaseChange φ D) x ≅
      moduleEvaluation A D (show D from x) ⋙ extension φ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    simp)

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionModuleMaps

/-! ## ScalarRestrictionHom（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarRestrictionHom.lean） -/

/-! # 係数制限による全次数 Hom の比較 -/

@[expose] public section ScalarRestrictionHom
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

instance restrictionLaxMonoidal : (restriction φ).LaxMonoidal :=
  (adjunction φ).rightAdjointLaxMonoidal

instance adjunctionMonoidal : (adjunction φ).IsMonoidal := inferInstance

/-- 斉次射の各成分を係数制限する。 -/
abbrev restrictCochain {K L : Complex A'} {p : ℤ} (f : Homogeneous K L p) :
    Homogeneous ((restriction φ).obj K) ((restriction φ).obj L) p :=
  f.map (ModuleCat.restrictScalars φ)

/-- 全次数 Hom を、係数制限した複体の間の Hom に送る。 -/
def restrictionHom (K L : Complex A') :
    (restriction φ).obj (homComplex A' K L) ⟶
      homComplex A ((restriction φ).obj K) ((restriction φ).obj L) where
  f p := ModuleCat.ofHom
    (X := ((restriction φ).obj (homComplex A' K L)).X p)
    (Y := (homComplex A ((restriction φ).obj K) ((restriction φ).obj L)).X p) {
    toFun := restrictCochain φ
    map_add' f g := Cochain.map_add f g (ModuleCat.restrictScalars φ)
    map_smul' a f := by
      apply Cochain.ext
      intro i j h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (φ a) • f.v i j h x = (φ a) • f.v i j h x
      rfl }
  comm' p q _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact δ_map p q f (ModuleCat.restrictScalars φ) |>.symm

lemma restrictionHom_v (K L : Complex A') (p i j : ℤ) (h : i + p = j)
    (f : Homogeneous K L p) :
    ((restrictionHom φ K L).f p f).v i j h = (ModuleCat.restrictScalars φ).map (f.v i j h) := rfl

set_option backward.isDefEq.respectTransparency true in
lemma restriction_μ_apply (K L : Complex A') (p q n : ℤ) (h : p + q = n)
    (x : K.X p) (y : L.X q) :
    (Functor.LaxMonoidal.μ (restriction φ) K L).f n
      (ιTensorObj ((restriction φ).obj K) ((restriction φ).obj L) p q n h (x ⊗ₜ[A] y)) =
        ιTensorObj K L p q n h (x ⊗ₜ[A'] y) := by
  let := φ.toAlgebra
  change ((adjunction φ).counit.app K ⊗ₘ (adjunction φ).counit.app L).f n
    ((tensorIso φ ((restriction φ).obj K) ((restriction φ).obj L)).hom.f n
      ((1 : A') ⊗ₜ[A]
        ιTensorObj ((restriction φ).obj K) ((restriction φ).obj L) p q n h (x ⊗ₜ[A] y))) = _
  erw [cochainTensorBaseChangeIso_apply_ι φ ((restriction φ).obj K) ((restriction φ).obj L),
    tensorMap_apply]
  congr 1
  change ((ModuleCat.extendRestrictScalarsAdj φ).counit.app (K.X p) ((1 : A') ⊗ₜ[A] x)) ⊗ₜ[A']
    ((ModuleCat.extendRestrictScalarsAdj φ).counit.app (L.X q) ((1 : A') ⊗ₜ[A] y)) = _
  erw [ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul φ,
    ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul φ]

set_option backward.isDefEq.respectTransparency true in
lemma restriction_ε_one :
    (Functor.LaxMonoidal.ε (restriction φ)).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) =
        (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A'))).inv (1 : A') := by
  let := φ.toAlgebra
  change (unitIso φ).hom.f 0
    ((1 : A') ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) = _
  exact sphereIso_one φ 0

lemma restrictCochain_units_smul {K L : Complex A'} {p : ℤ}
    (a : ℤˣ) (f : Homogeneous K L p) :
    restrictCochain φ (a • f) = a • restrictCochain φ f := by
  apply Cochain.ext
  intro i j h
  simp only [restrictCochain, Cochain.map_v, Cochain.units_smul_v,
    CategoryTheory.Functor.map_units_smul]

lemma restrictionHom_identity (K : Complex A') :
    Functor.LaxMonoidal.ε (restriction φ) ≫ (restriction φ).map (identity K) ≫
      restrictionHom φ K K = identity ((restriction φ).obj K) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change restrictCochain φ ((identity K).f 0
    ((Functor.LaxMonoidal.ε (restriction φ)).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)))) = _
  rw [restriction_ε_one]
  have hid : (identity K).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A'))).inv (1 : A')) = Cochain.ofHom (𝟙 K) := by
    exact congrArg Subtype.val (cycleFromUnit_unitFromCycle _ _)
  rw [hid]
  change (Cochain.ofHom (𝟙 K)).map (ModuleCat.restrictScalars φ) =
    (cycleFromUnit _ (identity ((restriction φ).obj K))).val
  rw [Cochain.map_ofHom, CategoryTheory.Functor.map_id, identity, cycleFromUnit_unitFromCycle]

lemma restrictionHom_composition (K L M : Complex A') :
    Functor.LaxMonoidal.μ (restriction φ) (homComplex A' K L) (homComplex A' L M) ≫
        (restriction φ).map (enrichedComposition K L M) ≫ restrictionHom φ K M =
      (restrictionHom φ K L ⊗ₘ restrictionHom φ L M) ≫
        enrichedComposition ((restriction φ).obj K) ((restriction φ).obj L)
          ((restriction φ).obj M) := by
  apply tensorHom_ext
  intro p q n h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change restrictCochain φ ((enrichedComposition K L M).f n
    ((Functor.LaxMonoidal.μ (restriction φ) (homComplex A' K L) (homComplex A' L M)).f n
      (ιTensorObj ((restriction φ).obj (homComplex A' K L))
        ((restriction φ).obj (homComplex A' L M))
        p q n h (f ⊗ₜ[A] g)))) =
    (enrichedComposition _ _ _).f n
      ((restrictionHom φ K L ⊗ₘ restrictionHom φ L M).f n
        (ιTensorObj ((restriction φ).obj (homComplex A' K L))
        ((restriction φ).obj (homComplex A' L M))
          p q n h (f ⊗ₜ[A] g)))
  rw [restriction_μ_apply, enrichedComposition_apply, tensorMap_apply, enrichedComposition_apply]
  rw [restrictCochain_units_smul]
  change (p * q).negOnePow • ((Cochain.comp f g h).map (ModuleCat.restrictScalars φ)) =
    (p * q).negOnePow • (f.map (ModuleCat.restrictScalars φ)).comp
      (g.map (ModuleCat.restrictScalars φ)) h
  rw [Cochain.map_comp]

/-- 係数制限は、移送した自己豊穣構造からの dg 関手を与える。 -/
def restrictionComplexDGFunctor :
    DGFunctor A (TransportEnrichment (restriction φ) (Complex A')) (Complex A) where
  obj := (restriction φ).obj
  map K L := restrictionHom φ K L
  map_id K := restrictionHom_identity φ K
  map_comp K L M := restrictionHom_composition φ K L M

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarRestrictionHom

/-! ## ScalarRestrictionCategory（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarRestrictionCategory.lean） -/

/-! # dg 圏の係数制限と係数変更の単位 -/

@[expose] public section ScalarRestrictionCategory
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

abbrev DGRestriction (C : Type v) [DGCategory A' C] := TransportEnrichment (restriction φ) C

def restrictDGFunctor {C : Type v} {E : Type w} [DGCategory A' C] [DGCategory A' E]
    (F : DGFunctor A' C E) : DGFunctor A (DGRestriction φ C) (DGRestriction φ E) where
  obj := F.obj
  map x y := (restriction φ).map (F.map x y)
  map_id x := by
    change Functor.LaxMonoidal.ε (restriction φ) ≫
      (restriction φ).map (eId (Complex A') (C := C) x) ≫ (restriction φ).map (F.map x x) = _
    rw [← CategoryTheory.Functor.map_comp, F.map_id]
    rfl
  map_comp x y z := by
    change Functor.LaxMonoidal.μ (restriction φ) _ _ ≫
      (restriction φ).map (eComp (Complex A') (C := C) x y z) ≫
        (restriction φ).map (F.map x z) = _
    rw [← CategoryTheory.Functor.map_comp, F.map_comp, CategoryTheory.Functor.map_comp,
      ← Functor.LaxMonoidal.μ_natural_assoc]
    rfl

/-- モノイダル随伴の単位は、dg 圏の Hom の係数変更への dg 関手を与える。 -/
def unitDGFunctor (D : Type v) [DGCategory A D] :
    DGFunctor A D (DGRestriction φ (DGBaseChange φ D)) where
  obj x := x
  map x y := (adjunction φ).unit.app (homObject A D x y)
  map_id x := by
    have hu := NatTrans.IsMonoidal.unit (τ := (adjunction φ).unit)
    change 𝟙 _ ≫ (adjunction φ).unit.app (𝟙_ (Complex A)) =
      Functor.LaxMonoidal.ε (restriction φ) ≫ (restriction φ).map (unitIso φ).inv at hu
    rw [Category.id_comp] at hu
    change eId (Complex A) (C := D) x ≫ (adjunction φ).unit.app _ =
      Functor.LaxMonoidal.ε (restriction φ) ≫
        (restriction φ).map ((unitIso φ).inv ≫ (extension φ).map (eId (Complex A) (C := D) x))
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← hu]
    exact (adjunction φ).unit.naturality (eId (Complex A) (C := D) x)
  map_comp x y z := by
    have ht := NatTrans.IsMonoidal.tensor (τ := (adjunction φ).unit)
      (homObject A D x y) (homObject A D y z)
    change 𝟙 _ ≫ (adjunction φ).unit.app (homObject A D x y ⊗ homObject A D y z) =
      ((adjunction φ).unit.app (homObject A D x y) ⊗ₘ
        (adjunction φ).unit.app (homObject A D y z)) ≫
      Functor.LaxMonoidal.μ (restriction φ) _ _ ≫
        (restriction φ).map (tensorIso φ _ _).inv at ht
    rw [Category.id_comp] at ht
    change eComp (Complex A) (C := D) x y z ≫ (adjunction φ).unit.app _ =
      ((adjunction φ).unit.app (homObject A D x y) ⊗ₘ
        (adjunction φ).unit.app (homObject A D y z)) ≫
      Functor.LaxMonoidal.μ (restriction φ) _ _ ≫
        (restriction φ).map ((tensorIso φ _ _).inv ≫
          (extension φ).map (eComp (Complex A) (C := D) x y z))
    rw [CategoryTheory.Functor.map_comp]
    exact ((adjunction φ).unit.naturality (eComp (Complex A) (C := D) x y z)).trans
      (by
        have ht' := congrArg (fun t => t ≫ (restriction φ).map ((extension φ).map
          (eComp (Complex A) (C := D) x y z))) ht
        simp only [Category.assoc] at ht'
        convert ht' using 1 <;> rfl)

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarRestrictionCategory

/-! ## ScalarRestrictionModule（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarRestrictionModule.lean） -/

/-! # dg 加群の係数制限 -/

@[expose] public section ScalarRestrictionModule
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

/-- opposite と係数拡大を交換する逆向きの dg 関手。 -/
def oppositeDGInverse :
    DGFunctor A' (DGBaseChange φ Dᵒᵖ) (DGBaseChange φ D)ᵒᵖ where
  obj x := op (show DGBaseChange φ D from x.unop)
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp x y z := by
    change ((tensorIso φ _ _).inv ≫ (extension φ).map
      ((β_ _ _).hom ≫ eComp (Complex A) (C := D) z.unop y.unop x.unop)) ≫ 𝟙 _ =
        (𝟙 _ ⊗ₘ 𝟙 _) ≫ (β_ _ _).hom ≫ (tensorIso φ _ _).inv ≫
          (extension φ).map (eComp (Complex A) (C := D) z.unop y.unop x.unop)
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp,
      CategoryTheory.Functor.map_comp]
    rw [tensorIso_braiding_assoc]

/-- 拡大後の左加群を、係数変更の単位に沿って制限する。 -/
def leftRestriction (M : LeftModule A' (DGBaseChange φ D)) : LeftModule A D :=
  (unitDGFunctor φ D).comp ((restrictDGFunctor φ M).comp (restrictionComplexDGFunctor φ))

/-- 拡大後の右加群を元の dg 圏上の右加群へ制限する。 -/
def rightRestriction (M : RightModule A' (DGBaseChange φ D)) : RightModule A D :=
  RightModule.ofFunctor (leftRestriction φ Dᵒᵖ ((oppositeDGInverse φ D).comp M.toFunctor))

lemma rightRestriction_obj (M : RightModule A' (DGBaseChange φ D)) (x : D) :
    (rightRestriction φ D M).obj (op x) = (restriction φ).obj (M.obj (op x)) := rfl

lemma leftRestriction_obj (M : LeftModule A' (DGBaseChange φ D)) (x : D) :
    (leftRestriction φ D M).obj x = (restriction φ).obj (M.obj x) := rfl

lemma rightRestriction_map (M : RightModule A' (DGBaseChange φ D)) (x y : Dᵒᵖ) :
    (rightRestriction φ D M).map x y = (adjunction φ).unit.app (x ⟶[Complex A] y) ≫
      (restriction φ).map (M.map x y) ≫ restrictionHom φ (M.obj x) (M.obj y) := by
  change (adjunction φ).unit.app _ ≫
    (restriction φ).map (𝟙 _ ≫ M.map x y) ≫ _ = _
  rw [Category.id_comp]
  rfl

lemma rightRestriction_action (M : RightModule A' (DGBaseChange φ D)) (x y : Dᵒᵖ)
    (p r n : ℤ) (h : r + p = n) (f : GradedHom A x y p) (m : (M.obj x).X r) :
    let := φ.toAlgebra
    moduleAction A (rightRestriction φ D M) (x := x) (y := y) f m h =
      moduleAction A' M (x := x) (y := y) ((1 : A') ⊗ₜ[A] f) m h := by
  let := φ.toAlgebra
  unfold moduleAction
  rw [rightRestriction_map]
  rfl

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarRestrictionModule

/-! ## ScalarRestrictionNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarRestrictionNaturality.lean） -/

/-! # 全次数 Hom の係数制限比較の自然性 -/

@[expose] public section ScalarRestrictionNaturality
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

@[reassoc]
lemma restrictionHom_postcompose (K : Complex A') {L L' : Complex A'} (g : L ⟶ L') :
    (restriction φ).map (homPostcompose K g) ≫ restrictionHom φ K L' =
      restrictionHom φ K L ≫ homPostcompose ((restriction φ).obj K) ((restriction φ).map g) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (f.comp (Cochain.ofHom g) (add_zero p)).map (ModuleCat.restrictScalars φ) =
    (f.map (ModuleCat.restrictScalars φ)).comp
      (Cochain.ofHom ((restriction φ).map g)) (add_zero p)
  rw [Cochain.map_comp, Cochain.map_ofHom]

@[reassoc]
lemma restrictionHom_precompose {K K' : Complex A'} (f : K' ⟶ K) (L : Complex A') :
    (restriction φ).map (homPrecompose f L) ≫ restrictionHom φ K' L =
      restrictionHom φ K L ≫ homPrecompose ((restriction φ).map f) ((restriction φ).obj L) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change ((Cochain.ofHom f).comp g (zero_add p)).map (ModuleCat.restrictScalars φ) =
    (Cochain.ofHom ((restriction φ).map f)).comp
      (g.map (ModuleCat.restrictScalars φ)) (zero_add p)
  rw [Cochain.map_comp, Cochain.map_ofHom]

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarRestrictionNaturality
