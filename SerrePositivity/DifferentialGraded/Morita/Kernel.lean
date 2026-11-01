module

public import SerrePositivity.DifferentialGraded.Derived.BimoduleLocal
public import SerrePositivity.DifferentialGraded.Module.FunctorExtension
public import SerrePositivity.DifferentialGraded.Verdier.Derived
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionTensorCoherence
public import SerrePositivity.DifferentialGraded.Derived.RightTensorLeftFunctor
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtension

/-!
# Morita.Kernel

## 概要
10 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w z u₁ u₂ v₁ v₂ w'

/-! ## KernelBasic（旧 SerrePositivity/DifferentialGraded/Morita/KernelBasic.lean） -/

/-! # Morita kernelの向きと主導来合成

## 概要
DからEの右加群導来圏への作用を表すkernelを、右E・左Dの導来bimoduleとして固定する。

## 方針
主bimodule局所化とU12e-localの既存合成を使い、新しい局所化型を作らない。

## 規約と注意
係数は任意可換環。対象宇宙は独立、Small.{u}を明示する。
合成は元の始域DのlocalHomKFlatだけを要求する。一般dg圏の分解をimportしない。

## 使われ方
U16aの作用・随伴・合成と、U16bのgraph比較から利用する。
受入範囲は`formalization-plans/archive/dg-theory-m5-status.md`を参照。
-/

@[expose] public section KernelBasic

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- D→Eのkernel。右E・左Dなので、bimoduleの添字はE・Dの順になる。 -/
abbrev Kernel := DerivedBimoduleCategory A E D

/-- 恒等作用のkernelは対角bimoduleの主導来像。局所Hom条件は不要。 -/
def kernelIdentity : Kernel A D D :=
  (bimoduleToDerived A D D).obj (BimoduleCategory.of A D D (Bimodule.diagonal A D))

/-- dg関手の延長を表すgraphの主導来像。値はHom_E(e,Fd)。 -/
def kernelGraph (F : DGFunctor A D E) : Kernel A D E :=
  (bimoduleToDerived A E D).obj (BimoduleCategory.of A E D (functorGraph A D E F))

variable (F : Type z) [DGCategory A F] [Small.{u} F]

/-- D→E、E→Fの順に適用するkernel合成。既存合成の出力側はDなのでhDのみを要求する。 -/
def kernelCompose (hD : localHomKFlat A D) (P : Kernel A D E) (Q : Kernel A E F) :
    Kernel A D F :=
  ((derivedBimoduleComposeFunctor A F E D hD).obj P).obj Q

/-- 両kernelの射による合成の射。既存curried主導来関手の作用を使う。 -/
def kernelComposeMap (hD : localHomKFlat A D)
    {P P' : Kernel A D E} {Q Q' : Kernel A E F} (f : P ⟶ P') (g : Q ⟶ Q') :
    kernelCompose A D E F hD P Q ⟶ kernelCompose A D E F hD P' Q' :=
  ((derivedBimoduleComposeFunctor A F E D hD).map f).app Q ≫
    ((derivedBimoduleComposeFunctor A F E D hD).obj P').map g

end SerrePositivity.DifferentialGraded.Morita
end

end KernelBasic

/-! ## KernelTensor（旧 SerrePositivity/DifferentialGraded/Morita/KernelTensor.lean） -/

/-! # 任意の指定bimoduleによる通常の加群tensor作用

## 概要
右E・左Dのkernelを右D加群にtensorして右E加群を得るdg関手。

## 方針
既存bimodule合成の後因子を右D加群圏の恒等dg関手として評価する。

## 規約と注意
全加群型のsmallnessやHomのK-flat性は要求しない。dg圏D・EのSmall.{u}のみ明示する。
これはunderived作用であり、任意kernelとのtensorが準同型を保存するとは主張しない。

## 使われ方
U16aの入力加群のsemifree解像度による導来作用と、U16bのgraph延長比較に使う。
-/

@[expose] public section KernelTensor

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 任意kernel Pによる通常の右加群作用。入力加群を導来化する前のdg関手。 -/
def kernelTensor (P : Bimodule A E D) : DGFunctor A (RightModule A D) (RightModule A E) :=
  (BimoduleTensor.compose A E D (RightModule A D) P
    (DGFunctor.id (RightModule A D))).toFunctor

/-- tensor作用の値は既存balanced tensor。右D加群とkernelの左D評価をこの順で使う。 -/
lemma kernelTensor_value (P : Bimodule A E D) (M : RightModule A D) (e : E) :
    ((kernelTensor A D E P).obj M).obj (op e) =
      BalancedTensor.obj A D M (P.leftAt e) := rfl

/-- graph kernelの場合は既存のdg加群延長そのもの。公開関手を別モデルへ置き換えない。 -/
lemma kernelTensor_graph (F : DGFunctor A D E) :
    kernelTensor A D E (functorGraph A D E F) = dgModuleExtension A D E F := rfl

end SerrePositivity.DifferentialGraded.Morita
end

end KernelTensor

/-! ## CriterionPerfHomInduction（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfHomInduction.lean） -/

/-! # 厚い帰納に使う、指定始域からの Hom 比較の閉性 -/

@[expose] public section CriterionPerfHomInduction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Pretriangulated Preadditive
open scoped ZeroObject
variable {C : Type u₁} [Category.{v₁} C] {T : Type u₂} [Category.{v₂} T]
  [HasZeroObject C] [HasZeroObject T] [Preadditive C] [Preadditive T]
  [HasShift C ℤ] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated C] [Pretriangulated T]
  (F : C ⥤ T) [F.CommShift ℤ] [F.IsTriangulated] [F.Additive]

/-- U17 の Hom 比較の五項完全列の議論を、指定した一つの始域へ局所化する。 -/
lemma criterionPerfHomComparison_triangle (X : C) (t : Triangle C) (ht : t ∈ distTriang C)
    (h₁ : Function.Bijective (F.map (X := X) (Y := t.obj₁)))
    (h₃ : Function.Bijective (F.map (X := X) (Y := t.obj₃)))
    (h₁s : Function.Bijective (F.map (X := X) (Y := t.obj₁⟦(1 : ℤ)⟧)))
    (h₃s : Function.Bijective (F.map (X := X) (Y := t.obj₃⟦(-1 : ℤ)⟧))) :
    Function.Bijective (F.map (X := X) (Y := t.obj₂)) := by
  have hker : ∀ f : X ⟶ t.obj₂, F.map f = 0 → f = 0 := by
    intro f hf
    have hz : f ≫ t.mor₂ = 0 := h₃.1 (by
      rw [Functor.map_comp, hf, zero_comp, Functor.map_zero])
    obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ t ht f hz
    have haz : F.map a ≫ (F.mapTriangle.obj t.invRotate).mor₂ = 0 := by
      change F.map a ≫ F.map t.mor₁ = 0
      rw [← Functor.map_comp, ← ha, hf]
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ (F.mapTriangle.obj t.invRotate)
      (F.map_distinguished _ (inv_rot_of_distTriang _ ht)) (F.map a) haz
    obtain ⟨c, hc⟩ := h₃s.2 b
    have hac : a = c ≫ t.invRotate.mor₁ := h₁.1 (by
      rw [Functor.map_comp, hc]
      exact hb)
    rw [ha, hac, Category.assoc]
    have hi : t.invRotate.mor₁ ≫ t.mor₁ = 0 :=
      comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ ht)
    rw [hi, comp_zero]
  constructor
  · intro f g hfg
    have hz : F.map (f - g) = 0 := by rw [Functor.map_sub, hfg, sub_self]
    exact sub_eq_zero.mp (hker (f - g) hz)
  · intro f
    obtain ⟨c, hc⟩ := h₃.2 (f ≫ F.map t.mor₂)
    have hz : c ≫ t.mor₃ = 0 := h₁s.1 (by
      rw [Functor.map_comp, hc, Category.assoc, ← Functor.map_comp,
        comp_distTriang_mor_zero₂₃ _ ht, Functor.map_zero, comp_zero]
      exact (F.map_zero _ _).symm)
    obtain ⟨d, hd⟩ := Triangle.coyoneda_exact₃ t ht c hz
    have hdiff : (f - F.map d) ≫ (F.mapTriangle.obj t).mor₂ = 0 := by
      change (f - F.map d) ≫ F.map t.mor₂ = 0
      rw [sub_comp, ← Functor.map_comp, ← hd, hc, sub_self]
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ (F.mapTriangle.obj t)
      (F.map_distinguished _ ht) (f - F.map d) hdiff
    obtain ⟨a, ha⟩ := h₁.2 b
    refine ⟨d + a ≫ t.mor₁, ?_⟩
    rw [Functor.map_add, Functor.map_comp, ha]
    have hb' : f - F.map d = b ≫ F.map t.mor₁ := hb
    rw [← hb']
    abel

/-- 指定した始域の族に関する全単射性。 -/
def criterionPerfRelativeHomTargets (S : ObjectProperty C) : ObjectProperty C :=
  fun Y => ∀ X, S X → Function.Bijective (F.map (X := X) (Y := Y))

variable (S : ObjectProperty C) [S.IsClosedUnderIsomorphisms] [S.IsStableUnderShift ℤ]

instance criterionPerfRelativeHomTargetsClosedUnderIso :
    (criterionPerfRelativeHomTargets F S).IsClosedUnderIsomorphisms where
  of_iso e h X hX := homComparison_bijective_of_iso F (Iso.refl X) e (h X hX)

instance criterionPerfRelativeHomTargetsShift :
    (criterionPerfRelativeHomTargets F S).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun Y h X hX => by
    let X' := (shiftFunctor C n).objPreimage X
    have hX' : S X' := (S.prop_shift_iff_of_isStableUnderShift X' n).1
      (S.prop_of_iso ((shiftFunctor C n).objObjPreimageIso X).symm hX)
    exact homComparison_bijective_of_iso F ((shiftFunctor C n).objObjPreimageIso X)
      (Iso.refl (Y⟦n⟧)) (homComparison_bijective_shift_both F (h X' hX') n)⟩

instance criterionPerfRelativeHomTargetsTriangulated :
    (criterionPerfRelativeHomTargets F S).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, fun X _ => by
    constructor
    · intro f g _
      exact (isZero_zero C).eq_of_tgt f g
    · intro f
      exact ⟨0, (F.map_isZero (isZero_zero C)).eq_of_tgt _ _⟩⟩
  toIsTriangulatedClosed₂ := .mk' (fun t ht h₁ h₃ X hX =>
    criterionPerfHomComparison_triangle F X t ht (h₁ X hX) (h₃ X hX)
      ((criterionPerfRelativeHomTargets F S).le_shift (1 : ℤ) _ h₁ X hX)
      ((criterionPerfRelativeHomTargets F S).le_shift (-1 : ℤ) _ h₃ X hX))

instance criterionPerfRelativeHomTargetsRetracts :
    (criterionPerfRelativeHomTargets F S).IsStableUnderRetracts where
  of_retract a h X hX := by
    constructor
    · intro f g hfg
      have he : f ≫ a.i = g ≫ a.i := (h X hX).1 (by
        rw [F.map_comp, F.map_comp, hfg])
      have := congrArg (fun k => k ≫ a.r) he
      simpa only [Category.assoc, a.retract, Category.comp_id] using this
    · intro g
      obtain ⟨f, hf⟩ := (h X hX).2 (g ≫ F.map a.i)
      refine ⟨f ≫ a.r, ?_⟩
      rw [F.map_comp, hf, Category.assoc, ← F.map_comp, a.retract, F.map_id,
        Category.comp_id]

omit [HasZeroObject C] [HasZeroObject T] [Preadditive C] [Preadditive T]
    [HasShift C ℤ] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor T n).Additive]
    [Pretriangulated C] [Pretriangulated T] [F.CommShift ℤ] [F.IsTriangulated] [F.Additive] in
/-- 反対圏を使って同じ帰納を始域にも適用するための全単射性の移送。 -/
lemma criterionPerfHomComparison_op_iff (X Y : C) :
    Function.Bijective (F.op.map (X := Opposite.op Y) (Y := Opposite.op X)) ↔
      Function.Bijective (F.map (X := X) (Y := Y)) := by
  constructor
  · intro h
    constructor
    · intro f g he
      exact congrArg Quiver.Hom.unop (h.1 (congrArg Quiver.Hom.op he))
    · intro f
      obtain ⟨g, hg⟩ := h.2 f.op
      exact ⟨g.unop, congrArg Quiver.Hom.unop hg⟩
  · intro h
    constructor
    · intro f g he
      exact congrArg Quiver.Hom.op (h.1 (congrArg Quiver.Hom.unop he))
    · intro f
      obtain ⟨g, hg⟩ := h.2 f.unop
      exact ⟨g.op, congrArg Quiver.Hom.op hg⟩

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfHomInduction

/-! ## ScalarExtensionTensorModels（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionTensorModels.lean） -/

/-! # U16d：二変数に自然な係数変更モデルとU12f計算の接続

hPN（A上のbalanced tensorのK-flat性）とhP'（係数変更した右加群の相対K-flat性）を
モデルの条件として分けて保持する。主導来kernel作用との接続はその実装後に行う。
-/

@[expose] public section ScalarExtensionTensorModels

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]

def scalarTensorKFlatModels : ObjectProperty (ModuleCategory A D × LeftModuleCategory A D) :=
  fun MN => complexKFlat A ((BalancedTensor.functor A D).obj MN) ∧
    moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) MN.1))

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

def scalarTensorModelSource :
    ModuleCategory A D × LeftModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A') :=
  BalancedTensor.functor A D ⋙ DerivedCategory.Q ⋙ complexDerivedExtension φ

def scalarTensorModelTarget :
    ModuleCategory A D × LeftModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A') :=
  (moduleExtension φ D).prod (leftModuleExtension φ D) ⋙
    BalancedTensor.functor A' (DGBaseChange φ D) ⋙ DerivedCategory.Q

def scalarTensorModelComparison : scalarTensorModelSource φ D ⟶ scalarTensorModelTarget φ D where
  app MN := derivedBalancedComparison φ D
    (ForgetEnrichment.to (Complex A) MN.1) (ForgetEnrichment.to (Complex A) MN.2)
  naturality _ _ fg := derivedBalancedComparison_naturality φ D fg.1 fg.2

/-- K-flatなモデルの充満部分圏では、両変数の全射に自然な同型となる。 -/
def scalarTensorModelBaseChangeIso :
    (scalarTensorKFlatModels φ D).ι ⋙ scalarTensorModelSource φ D ≅
      (scalarTensorKFlatModels φ D).ι ⋙ scalarTensorModelTarget φ D := by
  let α := Functor.whiskerLeft (scalarTensorKFlatModels φ D).ι (scalarTensorModelComparison φ D)
  have (X : (scalarTensorKFlatModels φ D).FullSubcategory) : IsIso (α.app X) :=
    derivedBalancedComparison_isIso φ D (ForgetEnrichment.to (Complex A) X.obj.1)
      (ForgetEnrichment.to (Complex A) X.obj.2) X.property.1
  letI := NatIso.isIso_of_isIso_app α
  exact asIso α

lemma scalarTensorModelBaseChangeIso_hom_app
    (X : (scalarTensorKFlatModels φ D).FullSubcategory) :
    (scalarTensorModelBaseChangeIso φ D).hom.app X =
      derivedBalancedComparison φ D (ForgetEnrichment.to (Complex A) X.obj.1)
        (ForgetEnrichment.to (Complex A) X.obj.2) := rfl

/-- U12fの実際の導来tensor比較を、自然な二変数モデルの比較と前後の計算同型で表す。 -/
lemma scalarTensorBaseChange_model_square {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) (N : LeftModule A D)
    (hPN : complexKFlat A (BalancedTensor.obj A D (ForgetEnrichment.to (Complex A) P.obj) N))
    (hP' : moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) P.obj))) :
    (derivedTensorBaseChange φ D P N hPN hP').hom =
      (complexDerivedExtension φ).map (moduleDerivedTensorRightResolutionComputation A D P N).hom ≫
        (scalarTensorModelBaseChangeIso φ D).hom.app
          ⟨(P.obj, ForgetEnrichment.of (Complex A) N), ⟨hPN, hP'⟩⟩ ≫
        (relativeKFlatTensorComputation (DGBaseChange φ D) ((moduleExtension φ D).obj P.obj)
          hP' (leftModule φ D N)).inv ≫
        (moduleDerivedTensorRight A' (DGBaseChange φ D) (leftModule φ D N)).map
          (derivedExtensionResolutionComputation φ D P).inv := by
  simp only [derivedTensorBaseChange, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    scalarTensorModelBaseChangeIso_hom_app, derivedBalancedComparison,
    complexDerivedExtensionKFlatIso, asIso_hom, Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionTensorModels

/-! ## ScalarExtensionTensorNaturality（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionTensorNaturality.lean） -/

/-! # U12f係数変更の計算同型と左因子の自然性 -/

@[expose] public section ScalarExtensionTensorNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma tensorResolutionComputation_left_naturality
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {N N' : LeftModuleCategory A D} (g : N ⟶ N') (M : ModuleCategory A D) :
    ((moduleResolutionDerivedTensorLeftFunctor A D R).map g).app ((moduleToDerived A D).obj M) ≫
        (moduleResolutionDerivedTensorComputation A D R
          (ForgetEnrichment.to (Complex A) N') M).hom =
      (moduleResolutionDerivedTensorComputation A D R
        (ForgetEnrichment.to (Complex A) N) M).hom ≫
          DerivedCategory.Q.map (BalancedTensor.map A D (𝟙 (R M).obj) g) := by
  let η := BalancedTensor.rightTensorHomotopyLeftMap A D g
  let e := moduleDerivedResolutionComputation A D R M
  have hn := congrArg DerivedCategory.Qh.map (η.naturality e.hom)
  simp only [CategoryTheory.Functor.map_comp] at hn
  simp only [moduleResolutionDerivedTensorComputation, Iso.trans_hom,
    Functor.mapIso_hom, moduleTensorHomotopyComputation, eqToIso.hom,
    eqToHom_refl, CategoryTheory.Functor.map_id]
  simp only [Functor.comp_map, Iso.app_hom]
  erw [Category.id_comp, Category.id_comp]
  change DerivedCategory.Qh.map (η.app _) ≫
      (DerivedCategory.Qh.map ((BalancedTensor.rightTensorHomotopyFunctor A D
        (ForgetEnrichment.to (Complex A) N')).map e.hom) ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app
        ((BalancedTensor.rightTensorFunctor A D
          (ForgetEnrichment.to (Complex A) N')).obj (R M).obj)) =
    (DerivedCategory.Qh.map ((BalancedTensor.rightTensorHomotopyFunctor A D
        (ForgetEnrichment.to (Complex A) N)).map e.hom) ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app
        ((BalancedTensor.rightTensorFunctor A D
          (ForgetEnrichment.to (Complex A) N)).obj (R M).obj)) ≫ _
  rw [← Category.assoc, ← hn, Category.assoc]
  dsimp [η]
  rw [BalancedTensor.rightTensorHomotopyLeftMap_app]
  erw [DerivedCategory.quotientCompQhIso_hom_naturality]
  exact (Category.assoc _ _ _).symm

lemma tensorProjectiveResolutionComputation_left_naturality
    {M : ModuleCategory A D} (R : ModuleProjectiveResolution A D M)
    {N N' : LeftModuleCategory A D} (g : N ⟶ N') :
    ((moduleDerivedTensorLeftFunctor A D).map g).app ((moduleToDerived A D).obj M) ≫
        (moduleDerivedTensorRightResolutionComputation A D R
          (ForgetEnrichment.to (Complex A) N')).hom =
      (moduleDerivedTensorRightResolutionComputation A D R
        (ForgetEnrichment.to (Complex A) N)).hom ≫
          DerivedCategory.Q.map (BalancedTensor.map A D (𝟙 R.obj) g) := by
  change ((moduleResolutionDerivedTensorLeftFunctor A D
    (moduleCanonicalProjectiveResolution A D)).map g).app _ ≫ _ = _
  simp only [moduleDerivedTensorRightResolutionComputation, Iso.trans_hom]
  rw [← Category.assoc,
    tensorResolutionComputation_left_naturality A D (moduleCanonicalProjectiveResolution A D) g M,
    Category.assoc, Category.assoc]
  congr 1
  simp only [moduleProjectiveResolutionTensorIso_hom, ← CategoryTheory.Functor.map_comp]
  congr 1
  change BalancedTensor.map A D (𝟙 _) g ≫
      BalancedTensor.map A D ((moduleCanonicalProjectiveResolution A D M).comparison R) (𝟙 N') =
    BalancedTensor.map A D ((moduleCanonicalProjectiveResolution A D M).comparison R) (𝟙 N) ≫
      BalancedTensor.map A D (𝟙 _) g
  simp only [← BalancedTensor.map_comp, Category.id_comp, Category.comp_id]

lemma relativeTensorComputation_left_naturality
    (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    {N N' : LeftModuleCategory A D} (g : N ⟶ N') :
    ((moduleDerivedTensorLeftFunctor A D).map g).app ((moduleToDerived A D).obj M) ≫
        (relativeKFlatTensorComputation D M hM (ForgetEnrichment.to (Complex A) N')).hom =
      (relativeKFlatTensorComputation D M hM (ForgetEnrichment.to (Complex A) N)).hom ≫
        DerivedCategory.Q.map (BalancedTensor.map A D (𝟙 M) g) := by
  change ((moduleResolutionDerivedTensorLeftFunctor A D
    (moduleCanonicalProjectiveResolution A D)).map g).app _ ≫ _ = _
  simp only [relativeKFlatTensorComputation, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc,
    tensorResolutionComputation_left_naturality A D (moduleCanonicalProjectiveResolution A D) g M,
    Category.assoc, Category.assoc]
  congr 1
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1
  change BalancedTensor.map A D (𝟙 _) g ≫
      BalancedTensor.map A D (moduleCanonicalProjectiveResolution A D M).π (𝟙 N') =
    BalancedTensor.map A D (moduleCanonicalProjectiveResolution A D M).π (𝟙 N) ≫
      BalancedTensor.map A D (𝟙 M) g
  simp only [← BalancedTensor.map_comp, Category.id_comp, Category.comp_id]

private lemma conjugateIso_naturality {C : Type*} [Category* C]
    {X Y X₀ Y₀ U V U₀ V₀ : C}
    (c : X ≅ X₀) (c' : Y ≅ Y₀) (b : X₀ ≅ U₀) (b' : Y₀ ≅ V₀)
    (d : U ≅ U₀) (d' : V ≅ V₀)
    (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀) (g : U ⟶ V) (g₀ : U₀ ⟶ V₀)
    (hc : f ≫ c'.hom = c.hom ≫ f₀)
    (hb : f₀ ≫ b'.hom = b.hom ≫ g₀)
    (hd : g ≫ d'.hom = d.hom ≫ g₀) :
    f ≫ (c' ≪≫ b' ≪≫ d'.symm).hom = (c ≪≫ b ≪≫ d.symm).hom ≫ g := by
  apply (cancel_mono d'.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% hc, hb, hd]
  simp only [Iso.inv_hom_id_assoc]

variable {A} {A' : Type u} [CommRing A'] (φ : A →+* A')
  [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

set_option maxHeartbeats 600000 in
-- 二つの係数環・三つの計算同型を結ぶ図式の型の照合に、既定値より多い展開が必要。
lemma scalarTensorBaseChange_left_naturality
    {M : ModuleCategory A D} (R : ModuleProjectiveResolution A D M)
    {N N' : LeftModuleCategory A D} (g : N ⟶ N')
    (hPN : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) R.obj) (ForgetEnrichment.to (Complex A) N)))
    (hPN' : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) R.obj) (ForgetEnrichment.to (Complex A) N')))
    (hP' : moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) R.obj))) :
    (complexDerivedExtension φ).map
        (((moduleDerivedTensorLeftFunctor A D).map g).app ((moduleToDerived A D).obj M)) ≫
        (derivedTensorBaseChange φ D R (ForgetEnrichment.to (Complex A) N') hPN' hP').hom =
      (derivedTensorBaseChange φ D R (ForgetEnrichment.to (Complex A) N) hPN hP').hom ≫
        ((moduleDerivedTensorLeftFunctor A' (DGBaseChange φ D)).map
          ((leftModuleExtension φ D).map g)).app
            ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)) := by
  let c (L : LeftModuleCategory A D) := (complexDerivedExtension φ).mapIso
    (moduleDerivedTensorRightResolutionComputation A D R (ForgetEnrichment.to (Complex A) L))
  let d (L : LeftModuleCategory A D) :=
    (moduleDerivedTensorRight A' (DGBaseChange φ D)
      (leftModule φ D (ForgetEnrichment.to (Complex A) L))).mapIso
        (derivedExtensionResolutionComputation φ D R) ≪≫
      relativeKFlatTensorComputation (DGBaseChange φ D) ((moduleExtension φ D).obj R.obj)
        hP' (leftModule φ D (ForgetEnrichment.to (Complex A) L))
  let X : (scalarTensorKFlatModels φ D).FullSubcategory :=
    ⟨(R.obj, N), ⟨hPN, hP'⟩⟩
  let Y : (scalarTensorKFlatModels φ D).FullSubcategory :=
    ⟨(R.obj, N'), ⟨hPN', hP'⟩⟩
  let b := (scalarTensorModelBaseChangeIso φ D).app X
  let b' := (scalarTensorModelBaseChangeIso φ D).app Y
  have hc := congrArg (complexDerivedExtension φ).map
    (tensorProjectiveResolutionComputation_left_naturality A D R g)
  simp only [CategoryTheory.Functor.map_comp] at hc
  have hd : ((moduleDerivedTensorLeftFunctor A' (DGBaseChange φ D)).map
          ((leftModuleExtension φ D).map g)).app
          ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)) ≫ (d N').hom =
      (d N).hom ≫ DerivedCategory.Q.map (BalancedTensor.map A' (DGBaseChange φ D)
        (𝟙 ((moduleExtension φ D).obj R.obj)) ((leftModuleExtension φ D).map g)) := by
    dsimp only [d, Iso.trans_hom, Functor.mapIso_hom]
    have ht := ((moduleDerivedTensorLeftFunctor A' (DGBaseChange φ D)).map
      ((leftModuleExtension φ D).map g)).naturality
        (derivedExtensionResolutionComputation φ D R).hom
    rw [← Category.assoc]
    erw [← ht]
    rw [Category.assoc]
    erw [relativeTensorComputation_left_naturality A' (DGBaseChange φ D)
      ((moduleExtension φ D).obj R.obj) hP' ((leftModuleExtension φ D).map g)]
    exact (Category.assoc _ _ _).symm
  have hb := (scalarTensorModelBaseChangeIso φ D).hom.naturality
    (ObjectProperty.homMk (𝟙 R.obj, g) : X ⟶ Y)
  change (complexDerivedExtension φ).map (DerivedCategory.Q.map
      (BalancedTensor.map A D (𝟙 R.obj) g)) ≫ b'.hom =
    b.hom ≫ DerivedCategory.Q.map (BalancedTensor.map A' (DGBaseChange φ D)
      ((moduleExtension φ D).map (𝟙 R.obj)) ((leftModuleExtension φ D).map g)) at hb
  have hn : (derivedTensorBaseChange φ D R
      (ForgetEnrichment.to (Complex A) N) hPN hP').hom =
        ((c N) ≪≫ b ≪≫ (d N).symm).hom := by
    rw [scalarTensorBaseChange_model_square]
    simp only [c, b, d, X, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, ForgetEnrichment.of_to]
  have hn' : (derivedTensorBaseChange φ D R
      (ForgetEnrichment.to (Complex A) N') hPN' hP').hom =
        ((c N') ≪≫ b' ≪≫ (d N').symm).hom := by
    rw [scalarTensorBaseChange_model_square]
    simp only [c, b', d, Y, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, ForgetEnrichment.of_to]
  rw [hn, hn']
  refine conjugateIso_naturality (C := DerivedCategory (ModuleCat.{u} A'))
    (c N) (c N') b b' (d N) (d N')
    ((complexDerivedExtension φ).map
      (((moduleDerivedTensorLeftFunctor A D).map g).app ((moduleToDerived A D).obj M)))
    ((complexDerivedExtension φ).map
      (DerivedCategory.Q.map (BalancedTensor.map A D (𝟙 R.obj) g)))
    (((moduleDerivedTensorLeftFunctor A' (DGBaseChange φ D)).map
      ((leftModuleExtension φ D).map g)).app
        ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)))
    (DerivedCategory.Q.map (BalancedTensor.map A' (DGBaseChange φ D)
      (𝟙 ((moduleExtension φ D).obj R.obj)) ((leftModuleExtension φ D).map g))) ?_ ?_ ?_
  · exact hc
  · erw [CategoryTheory.Functor.map_id] at hb
    exact hb
  · exact hd

/-- 指定解像度に対するhPNとhP'を両方保持する左因子のモデル条件。 -/
def scalarTensorLeftModels {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M) : ObjectProperty (LeftModuleCategory A D) :=
  fun N => scalarTensorKFlatModels φ D (R.obj, N)

def scalarTensorBaseChangeLeftSource (M : ModuleCategory A D) :
    LeftModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A') :=
  moduleDerivedTensorLeftFunctor A D ⋙
    (CategoryTheory.evaluation (DerivedModuleCategory A D) (DerivedCategory (ModuleCat.{u} A))).obj
      ((moduleToDerived A D).obj M) ⋙ complexDerivedExtension φ

def scalarTensorBaseChangeLeftTarget (M : ModuleCategory A D) :
    LeftModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A') :=
  leftModuleExtension φ D ⋙ moduleDerivedTensorLeftFunctor A' (DGBaseChange φ D) ⋙
    (CategoryTheory.evaluation (DerivedModuleCategory A' (DGBaseChange φ D))
      (DerivedCategory (ModuleCat.{u} A'))).obj
        ((derivedExtension φ D).obj ((moduleToDerived A D).obj M))

/-- U12fの実際の比較同型を、許容モデル上の全左因子射に自然に束ねる。 -/
def scalarTensorBaseChangeLeftIso {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M) :
    (scalarTensorLeftModels D φ R).ι ⋙ scalarTensorBaseChangeLeftSource D φ M ≅
      (scalarTensorLeftModels D φ R).ι ⋙ scalarTensorBaseChangeLeftTarget D φ M :=
  NatIso.ofComponents
    (fun N => derivedTensorBaseChange φ D R (ForgetEnrichment.to (Complex A) N.obj)
      N.property.1 N.property.2)
    (by
      intro N N' g
      exact scalarTensorBaseChange_left_naturality D φ R g.hom
        N.property.1 N'.property.1 N.property.2)

lemma scalarTensorBaseChangeLeftIso_app {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M)
    (N : (scalarTensorLeftModels D φ R).FullSubcategory) :
    (scalarTensorBaseChangeLeftIso D φ R).app N =
      derivedTensorBaseChange φ D R (ForgetEnrichment.to (Complex A) N.obj)
        N.property.1 N.property.2 := rfl

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionTensorNaturality

/-! ## KernelResolution（旧 SerrePositivity/DifferentialGraded/Morita/KernelResolution.lean） -/

/-! # 通常kernelの主導来作用と入力解像度の選択比較

## 概要
右D入力を射影解像して、任意の右E・左D kernelによる主導来作用を構成する。

## 方針
U10の解像度関手と選択比較を、既存のtensor dg関手のH⁰関手へ送る。

## 規約と注意
任意可換環・非有界、D・EのSmall.{u}を明示する。局所Hom K-flat条件は不要。
kernel自体の準同型局所化への降下と一般右随伴は、このファイルではまだ構成しない。

## 使われ方
U16aのkernelDerivedTensorFunctorの構成と、U16bのgraph作用比較の計算に使う。
受入範囲は`formalization-plans/archive/dg-theory-m5-status.md`を参照。
-/

@[expose] public section KernelResolution

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- tensorのH⁰関手を主導来局所化へ送る。準同型保存は入力を射影解像して用いる。 -/
def kernelHomotopyToDerived : ModuleHomotopyCategory A D ⥤ DerivedModuleCategory A E :=
  (kernelTensor A D E P).onHomotopy ⋙ moduleHomotopyToDerivedClosed A E

/-- 指定した任意の入力射影解像度族によるkernel作用。 -/
def kernelResolutionDerivedTensor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A E :=
  moduleDerivedResolutionFunctor A D R ⋙ kernelHomotopyToDerived A D E P

/-- 標準semifree入力解像度による、通常kernelの主導来作用。 -/
def kernelDerivedTensorOnBimodule : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E :=
  kernelResolutionDerivedTensor A D E P (moduleCanonicalProjectiveResolution A D)

/-- 元の入力でH⁰計算を主局所化の計算に比較する。既存onHomotopy_facを使う。 -/
def kernelTensorHomotopyComputation (M : ModuleCategory A D) :
    (kernelHomotopyToDerived A D E P).obj ((moduleToHomotopy A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj M) :=
  (moduleHomotopyToDerivedClosed A E).mapIso
      (eqToIso (congrArg (fun G => G.obj M) (kernelTensor A D E P).onHomotopy_fac)) ≪≫
    (moduleToHomotopyDerivedIso A E).app ((kernelTensor A D E P).onClosed.obj M)

/-- 指定解像度族の作用は、その入力解像度との通常tensorで計算できる。 -/
def kernelResolutionDerivedTensorComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (kernelResolutionDerivedTensor A D E P R).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj (R M).obj) :=
  (kernelHomotopyToDerived A D E P).mapIso (moduleDerivedResolutionComputation A D R M) ≪≫
    kernelTensorHomotopyComputation A D E P (R M).obj

/-- 任意の二つの入力解像度族によるkernel作用は自然同型。 -/
def kernelResolutionDerivedTensorIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    kernelResolutionDerivedTensor A D E P R ≅ kernelResolutionDerivedTensor A D E P S :=
  Functor.isoWhiskerRight (moduleDerivedResolutionIso A D R S)
    (kernelHomotopyToDerived A D E P)

/-- 解像度族を変えないときの比較は恒等。U10の自己比較を送る。 -/
lemma kernelResolutionDerivedTensorIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    kernelResolutionDerivedTensorIso A D E P R R = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (kernelHomotopyToDerived A D E P).map
    ((moduleDerivedResolutionIso A D R R).hom.app X) = 𝟙 _
  rw [moduleDerivedResolutionIso_self]
  exact (kernelHomotopyToDerived A D E P).map_id _

/-- 三つの解像度族の比較は推移的。比較射を新たに選ばずU10の推移則を使う。 -/
lemma kernelResolutionDerivedTensorIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    kernelResolutionDerivedTensorIso A D E P R S ≪≫
        kernelResolutionDerivedTensorIso A D E P S T =
      kernelResolutionDerivedTensorIso A D E P R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (kernelHomotopyToDerived A D E P).map
      ((moduleDerivedResolutionIso A D R S).hom.app X) ≫
    (kernelHomotopyToDerived A D E P).map
      ((moduleDerivedResolutionIso A D S T).hom.app X) = _
  rw [← Functor.map_comp]
  exact congrArg (kernelHomotopyToDerived A D E P).map
    (NatTrans.congr_app (congrArg Iso.hom (moduleDerivedResolutionIso_trans A D R S T)) X)

/-- 標準作用も、単独の任意指定入力解像度で計算できる。 -/
def kernelDerivedTensorOnBimoduleComputation {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M) :
    (kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj R.obj) := by
  let S := moduleCanonicalProjectiveResolution A D
  let e := @asIso _ _ _ _ ((moduleToHomotopy A D).map ((S M).comparison R))
    ((S M).comparison_isIso_homotopy R)
  exact (kernelHomotopyToDerived A D E P).mapIso
      (moduleDerivedResolutionComputation A D S M ≪≫ e) ≪≫
    kernelTensorHomotopyComputation A D E P R.obj

/-- graphの場合は既存の主導来延長と同じ関手。U16bの計算入口。 -/
lemma kernelDerivedTensorOnBimodule_graph (F : DGFunctor A D E) :
    kernelDerivedTensorOnBimodule A D E (functorGraph A D E F) =
      dgDerivedExtension A D E F := rfl

end SerrePositivity.DifferentialGraded.Morita
end

end KernelResolution

/-! ## KernelNaturality（旧 SerrePositivity/DifferentialGraded/Morita/KernelNaturality.lean） -/

/-! # kernelの閉零射によるtensor作用の自然変換

## 概要
全Hom自然なkernel射を、入力加群にも自然なtensor作用の射へ送る。

## 方針
既存のbimodule合成射を右D加群圏の恒等dg関手で評価し、全Hom自然性を閉零射で評価する。

## 規約と注意
全右加群型にsmallnessを課さず、D・EのSmall.{u}だけを用いる。局所Hom条件は不要。

## 使われ方
U16aの主導来kernel上の関手族を構成するための通常・H⁰の自然性。
受入範囲は`formalization-plans/archive/dg-theory-m5-status.md`を参照。
-/

@[expose] public section KernelNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A]

private lemma homEquiv_post {V : Type*} [Category* V] [MonoidalCategory V]
    {C : Type*} [Category* C] [EnrichedOrdinaryCategory V C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) = eHomEquiv V f ≫ eHomWhiskerLeft V X g := by
  rw [eHomEquiv_comp]
  dsimp only [eHomWhiskerLeft]
  rw [rightUnitor_inv_naturality_assoc]
  simp only [unitors_inv_equal, tensorHom_def, Category.assoc]

private lemma homEquiv_pre {V : Type*} [Category* V] [MonoidalCategory V]
    {C : Type*} [Category* C] [EnrichedOrdinaryCategory V C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) = eHomEquiv V g ≫ eHomWhiskerRight V f Z := by
  rw [eHomEquiv_comp]
  dsimp only [eHomWhiskerRight]
  rw [leftUnitor_inv_naturality_assoc]
  simp only [tensorHom_def', Category.assoc]

/-- 全Hom自然な加群値bimodule射を閉零関手の自然変換へ評価する。源Cのsmallnessは不要。 -/
def kernelClosedFamilyNatTrans (E : Type w) [DGCategory A E] [Small.{u} E]
    (C : Type z) [DGCategory A C] {P Q : BimoduleCategory A E C} (a : P ⟶ Q) :
    (BimoduleCategory.underlying A E C P).toFunctor.onClosed ⟶
      (BimoduleCategory.underlying A E C Q).toFunctor.onClosed where
  app X := a.val (ForgetEnrichment.to (Complex A) X)
  naturality {X Y} f := by
    have h := congrArg (fun k => ForgetEnrichment.homTo (Complex A) f ≫ k)
      (a.property (ForgetEnrichment.to (Complex A) X) (ForgetEnrichment.to (Complex A) Y))
    apply (eHomEquiv (Complex A)).injective
    rw [homEquiv_post, homEquiv_pre]
    change (ForgetEnrichment.homTo (Complex A) f ≫ _) ≫ _ =
      (ForgetEnrichment.homTo (Complex A) f ≫ _) ≫ _
    simp only [moduleHomPostcompose, moduleHomPrecompose] at h
    convert h using 1 <;> rfl

variable (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- kernel射を通常tensor作用の自然変換へ送る。大きい全加群圏のsmallnessは不要。 -/
def kernelTensorMap {P P' : BimoduleCategory A E D} (f : P ⟶ P') :
    (kernelTensor A D E (BimoduleCategory.underlying A E D P)).onClosed ⟶
      (kernelTensor A D E (BimoduleCategory.underlying A E D P')).onClosed :=
  kernelClosedFamilyNatTrans A E (RightModule A D)
    (BimoduleTensor.composeMap A E D (RightModule A D) f
      (𝟙 (BimoduleCategory.of A D (RightModule A D) (DGFunctor.id (RightModule A D)))))

/-- 閉零作用のkernel射を各入力で評価すると、既存bimodule合成射の成分になる。 -/
lemma kernelTensorMap_app {P P' : BimoduleCategory A E D} (f : P ⟶ P')
    (M : ModuleCategory A D) :
    (kernelTensorMap A D E f).app M =
      (BimoduleTensor.composeMap A E D (RightModule A D) f
        (𝟙 (BimoduleCategory.of A D (RightModule A D)
          (DGFunctor.id (RightModule A D))))).val (ForgetEnrichment.to (Complex A) M) := rfl

/-- 恒等kernel射の通常作用は恒等自然変換。 -/
lemma kernelTensorMap_id (P : BimoduleCategory A E D) :
    kernelTensorMap A D E (𝟙 P) = 𝟙 _ := by
  apply NatTrans.ext
  funext M
  exact congrArg (fun k => k.val (ForgetEnrichment.to (Complex A) M))
    (BimoduleTensor.composeMap_id A E D (RightModule A D) P
      (BimoduleCategory.of A D (RightModule A D) (DGFunctor.id (RightModule A D))))

/-- kernel射の合成は通常作用の自然変換の合成へ送られる。 -/
lemma kernelTensorMap_comp {P P' P'' : BimoduleCategory A E D}
    (f : P ⟶ P') (g : P' ⟶ P'') :
    kernelTensorMap A D E (f ≫ g) = kernelTensorMap A D E f ≫ kernelTensorMap A D E g := by
  apply NatTrans.ext
  funext M
  let I := BimoduleCategory.of A D (RightModule A D) (DGFunctor.id (RightModule A D))
  have h := BimoduleTensor.composeMap_comp A E D (RightModule A D) f g (𝟙 I) (𝟙 I)
  rw [Category.id_comp] at h
  exact congrArg (fun k => k.val (ForgetEnrichment.to (Complex A) M)) h

/-- H⁰商の普遍性で、kernel射の通常作用を入力のホモトピー圏へ降ろす。 -/
def kernelTensorHomotopyMap {P P' : BimoduleCategory A E D} (f : P ⟶ P') :
    (kernelTensor A D E (BimoduleCategory.underlying A E D P)).onHomotopy ⟶
      (kernelTensor A D E (BimoduleCategory.underlying A E D P')).onHomotopy :=
  CategoryTheory.Quotient.natTransLift (boundaryRelation A (RightModule A D))
    { app M := (moduleToHomotopy A E).map ((kernelTensorMap A D E f).app M)
      naturality := fun {M N} g => by
        change (moduleToHomotopy A E).map _ ≫ (moduleToHomotopy A E).map _ =
          (moduleToHomotopy A E).map _ ≫ (moduleToHomotopy A E).map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (moduleToHomotopy A E).map ((kernelTensorMap A D E f).naturality g) }

/-- 元の入力でのH⁰成分は、既存の通常kernel作用の射を商へ送ったもの。 -/
lemma kernelTensorHomotopyMap_app {P P' : BimoduleCategory A E D} (f : P ⟶ P')
    (M : ModuleCategory A D) :
    (kernelTensorHomotopyMap A D E f).app ((moduleToHomotopy A D).obj M) =
      (moduleToHomotopy A E).map ((kernelTensorMap A D E f).app M) := rfl

/-- H⁰上でも恒等kernel射は恒等に写る。 -/
lemma kernelTensorHomotopyMap_id (P : BimoduleCategory A E D) :
    kernelTensorHomotopyMap A D E (𝟙 P) = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  rcases X with ⟨M⟩
  change (moduleToHomotopy A E).map ((kernelTensorMap A D E (𝟙 P)).app M) = 𝟙 _
  rw [kernelTensorMap_id]
  exact (moduleToHomotopy A E).map_id _

/-- H⁰への降下はkernel射の合成を保つ。 -/
lemma kernelTensorHomotopyMap_comp {P P' P'' : BimoduleCategory A E D}
    (f : P ⟶ P') (g : P' ⟶ P'') :
    kernelTensorHomotopyMap A D E (f ≫ g) =
      kernelTensorHomotopyMap A D E f ≫ kernelTensorHomotopyMap A D E g := by
  apply NatTrans.ext
  funext X
  rcases X with ⟨M⟩
  change (moduleToHomotopy A E).map ((kernelTensorMap A D E (f ≫ g)).app M) =
    (moduleToHomotopy A E).map ((kernelTensorMap A D E f).app M) ≫
      (moduleToHomotopy A E).map ((kernelTensorMap A D E g).app M)
  rw [kernelTensorMap_comp]
  exact (moduleToHomotopy A E).map_comp _ _

/-- tensor作用のkernel射は、各値でid入力と左評価射のbalanced tensor mapに一致する。 -/
lemma kernelTensorMap_value {P P' : BimoduleCategory A E D} (f : P ⟶ P')
    (M : ModuleCategory A D) (e : E) :
    (moduleEvaluation A E e).map ((kernelTensorMap A D E f).app M) =
      BalancedTensor.map A D (𝟙 M) ((BimoduleCategory.leftEvaluation A E D e).map f) := by
  change (BimoduleCategory.valueEvaluation A E (RightModule A D) e
    (ForgetEnrichment.to (Complex A) M)).map
      (BimoduleTensor.composeMap A E D (RightModule A D) f
        (𝟙 (BimoduleCategory.of A D (RightModule A D)
          (DGFunctor.id (RightModule A D))))) = _
  rw [BimoduleTensor.composeMap_value_eval]
  unfold BimoduleTensor.composeValueMap
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- 射影的右D入力は相対K-flatなので、任意kernel準同型をtensor作用が保つ。 -/
lemma kernelTensorMap_projective_quasiIso {P P' : BimoduleCategory A E D}
    (f : P ⟶ P') (hf : BimoduleCategory.quasiIso A E D f)
    (M : ModuleCategory A D) (hM : moduleHomotopicallyProjective A D M) :
    moduleQuasiIso A E ((kernelTensorMap A D E f).app M) := by
  intro e
  rw [kernelTensorMap_value]
  exact moduleRelativeKFlat_preserves_leftQuasiIso A D
    (ForgetEnrichment.to (Complex A) M) (moduleHomotopicallyProjective_relativeKFlat A D hM)
    ((BimoduleCategory.leftEvaluation A E D e).map f)
    (BimoduleCategory.quasiIso_leftEvaluation A E D hf e)

end SerrePositivity.DifferentialGraded.Morita
end

end KernelNaturality

/-! ## KernelDerivedFunctor（旧 SerrePositivity/DifferentialGraded/Morita/KernelDerivedFunctor.lean） -/

/-! # 主導来kernel上の全導来tensor作用

## 概要
通常kernelの作用をkernelの準同型で局所化し、両変数が主導来対象である作用を構成する。

## 方針
射影的右D入力の相対K-flat性でkernel準同型の反転を証明し、指定bimodule局所化を使う。

## 規約と注意
局所Hom K-flat条件はこの作用に不要。D・Eは独立宇宙でSmall.{u}を明示する。
一般右随伴や合成比較の存在をここで仮定しない。

## 使われ方
U16aの主導来作用とU16b/dのgraph・Perf比較の共通入口。
受入範囲は`formalization-plans/archive/dg-theory-m5-status.md`のU16の行に従う。
-/

@[expose] public section KernelDerivedFunctor

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- kernelの閉零射を、指定入力解像度による主導来作用の自然変換へ送る。 -/
def kernelResolutionDerivedTensorMap
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {P P' : BimoduleCategory A E D} (f : P ⟶ P') :
    kernelResolutionDerivedTensor A D E (BimoduleCategory.underlying A E D P) R ⟶
      kernelResolutionDerivedTensor A D E (BimoduleCategory.underlying A E D P') R :=
  whiskerLeft (moduleDerivedResolutionFunctor A D R)
    (whiskerRight (kernelTensorHomotopyMap A D E f) (moduleHomotopyToDerivedClosed A E))

/-- 入力解像度での作用は恒等kernel射を恒等に送る。 -/
lemma kernelResolutionDerivedTensorMap_id
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (P : BimoduleCategory A E D) :
    kernelResolutionDerivedTensorMap A D E R (𝟙 P) = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  change (moduleHomotopyToDerivedClosed A E).map
    ((kernelTensorHomotopyMap A D E (𝟙 P)).app _) = 𝟙 _
  rw [kernelTensorHomotopyMap_id]
  exact (moduleHomotopyToDerivedClosed A E).map_id _

/-- 入力解像度での作用はkernel射の合成を保つ。 -/
lemma kernelResolutionDerivedTensorMap_comp
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {P P' P'' : BimoduleCategory A E D} (f : P ⟶ P') (g : P' ⟶ P'') :
    kernelResolutionDerivedTensorMap A D E R (f ≫ g) =
      kernelResolutionDerivedTensorMap A D E R f ≫
        kernelResolutionDerivedTensorMap A D E R g := by
  apply NatTrans.ext
  funext X
  change (moduleHomotopyToDerivedClosed A E).map
      ((kernelTensorHomotopyMap A D E (f ≫ g)).app _) =
    (moduleHomotopyToDerivedClosed A E).map ((kernelTensorHomotopyMap A D E f).app _) ≫
      (moduleHomotopyToDerivedClosed A E).map ((kernelTensorHomotopyMap A D E g).app _)
  rw [kernelTensorHomotopyMap_comp]
  exact (moduleHomotopyToDerivedClosed A E).map_comp _ _

/-- 入力解像度を通すと、任意kernel準同型の作用は全導来入力上で同型になる。 -/
lemma kernelResolutionDerivedTensorMap_isIso
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {P P' : BimoduleCategory A E D} (f : P ⟶ P')
    (hf : BimoduleCategory.quasiIso A E D f) :
    IsIso (kernelResolutionDerivedTensorMap A D E R f) := by
  let α := whiskerRight (kernelTensorHomotopyMap A D E f) (moduleHomotopyToDerivedClosed A E)
  have hbase (M : ModuleCategory A D) :
      IsIso ((kernelResolutionDerivedTensorMap A D E R f).app ((moduleToDerived A D).obj M)) := by
    have hq := kernelTensorMap_projective_quasiIso A D E f hf (R M).obj (R M).projective
    have hi : IsIso ((moduleHomotopyToDerivedClosed A E).map
        ((moduleToHomotopy A E).map ((kernelTensorMap A D E f).app (R M).obj))) :=
      Localization.inverts (moduleHomotopyToDerivedClosed A E) (moduleHomotopyQuasiIso A E) _
        ((moduleHomotopyQuasiIso_map_iff A E _).2 hq)
    have ha : IsIso (α.app ((moduleToHomotopy A D).obj (R M).obj)) := hi
    let := ha
    change IsIso (α.app ((moduleDerivedResolutionFunctor A D R).obj ((moduleToDerived A D).obj M)))
    rw [← α.naturality_2 (moduleDerivedResolutionComputation A D R M)]
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  let M := (moduleToDerived A D).objPreimage X
  let e := (moduleToDerived A D).objObjPreimageIso X
  have hi := hbase M
  let := hi
  rw [← (kernelResolutionDerivedTensorMap A D E R f).naturality_1 e]
  infer_instance

/-- 通常kernel全体から、主導来右加群上の作用関手への実際の関手。 -/
def kernelDerivedTensorOnBimoduleFunctor :
    BimoduleCategory A E D ⥤ (DerivedModuleCategory A D ⥤ DerivedModuleCategory A E) where
  obj P := kernelDerivedTensorOnBimodule A D E (BimoduleCategory.underlying A E D P)
  map f := kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D) f
  map_id P := kernelResolutionDerivedTensorMap_id A D E _ P
  map_comp f g := kernelResolutionDerivedTensorMap_comp A D E _ f g

/-- 通常kernelの作用関手は、指定objectwise準同型を自然同型へ送る。 -/
lemma kernelDerivedTensorOnBimoduleFunctor_inverts :
    (BimoduleCategory.quasiIso A E D).IsInvertedBy
      (kernelDerivedTensorOnBimoduleFunctor A D E) := by
  intro P P' f hf
  exact kernelResolutionDerivedTensorMap_isIso A D E _ f hf

/-- 指定bimodule局所化上の全導来tensor作用。両変数とも主導来圏上にある。 -/
def kernelDerivedTensorFunctor :
    Kernel A D E ⥤ (DerivedModuleCategory A D ⥤ DerivedModuleCategory A E) :=
  bimoduleDerivedLift A E D (kernelDerivedTensorOnBimoduleFunctor A D E)
    (kernelDerivedTensorOnBimoduleFunctor_inverts A D E)

/-- 主導来kernel上への降下は、通常kernel上の既存作用関手と可換する。 -/
lemma kernelDerivedTensorFunctor_fac :
    bimoduleToDerived A E D ⋙ kernelDerivedTensorFunctor A D E =
      kernelDerivedTensorOnBimoduleFunctor A D E :=
  bimoduleDerivedLift_fac A E D _ _

/-- 指定した任意の主導来kernelによる右加群の主導来作用。 -/
def kernelDerivedTensor (P : Kernel A D E) :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A E :=
  (kernelDerivedTensorFunctor A D E).obj P

/-- 通常kernelの局所化像では、全導来作用は既存の入力解像度による作用と自然同型。 -/
def kernelDerivedTensorOnBimoduleIso (P : BimoduleCategory A E D) :
    kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj P) ≅
      kernelDerivedTensorOnBimodule A D E (BimoduleCategory.underlying A E D P) :=
  (eqToIso (kernelDerivedTensorFunctor_fac A D E)).app P

/-- 全導来作用を、単独の任意指定入力射影解像度による通常tensorで計算する。 -/
def kernelDerivedTensorComputation (P : Bimodule A E D) (M : ModuleCategory A D)
    (R : ModuleProjectiveResolution A D M) :
    (kernelDerivedTensor A D E
        ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).obj
        ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj R.obj) :=
  (kernelDerivedTensorOnBimoduleIso A D E (BimoduleCategory.of A E D P)).app
      ((moduleToDerived A D).obj M) ≪≫
    kernelDerivedTensorOnBimoduleComputation A D E P R

end SerrePositivity.DifferentialGraded.Morita
end

end KernelDerivedFunctor

/-! ## KernelComparisonNaturality（旧 SerrePositivity/DifferentialGraded/Morita/KernelComparisonNaturality.lean） -/

/-! # 主導来kernel作用と通常kernel作用の比較の自然性

## 概要
主導来kernelを通常代表で計算する同型が、kernel射と二つの作用の水平合成に自然であることを示す。

## 方針
既存の局所化との関手等式を自然同型として用い、Mathlibのexchange則を適用する。

## 規約と注意
局所Hom K-flat条件は不要。全ての通常kernel射を扱う。

## 使われ方
U16aのK-flat代表上の合成比較を、主導来kernel全体に自然な同型へ降ろす。
-/

@[expose] public section KernelComparisonNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 通常代表での主導来作用の計算同型は、任意のkernel射に自然。 -/
lemma kernelDerivedTensorOnBimoduleIso_naturality
    {P P' : BimoduleCategory A E D} (f : P ⟶ P') :
    (kernelDerivedTensorFunctor A D E).map ((bimoduleToDerived A E D).map f) ≫
        (kernelDerivedTensorOnBimoduleIso A D E P').hom =
      (kernelDerivedTensorOnBimoduleIso A D E P).hom ≫
        kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D) f := by
  have h := (eqToIso (kernelDerivedTensorFunctor_fac A D E)).hom.naturality f
  simp only [Functor.comp_map] at h
  exact h

variable (F : Type z) [DGCategory A F] [Small.{u} F]

/-- 主導来作用の通常代表比較を水平合成した同型は、両kernel射に自然。 -/
lemma kernelDerivedTensorOnBimoduleIso_hcomp_naturality
    {P P' : BimoduleCategory A E D} {Q Q' : BimoduleCategory A F E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    NatTrans.hcomp
        ((kernelDerivedTensorFunctor A D E).map ((bimoduleToDerived A E D).map f))
        ((kernelDerivedTensorFunctor A E F).map ((bimoduleToDerived A F E).map g)) ≫
        (NatIso.hcomp (kernelDerivedTensorOnBimoduleIso A D E P')
          (kernelDerivedTensorOnBimoduleIso A E F Q')).hom =
      (NatIso.hcomp (kernelDerivedTensorOnBimoduleIso A D E P)
          (kernelDerivedTensorOnBimoduleIso A E F Q)).hom ≫
        NatTrans.hcomp
          (kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D) f)
          (kernelResolutionDerivedTensorMap A E F (moduleCanonicalProjectiveResolution A E) g) := by
  simp only [NatIso.hcomp_hom]
  rw [← NatTrans.exchange, kernelDerivedTensorOnBimoduleIso_naturality,
    kernelDerivedTensorOnBimoduleIso_naturality, NatTrans.exchange]

end SerrePositivity.DifferentialGraded.Morita
end

end KernelComparisonNaturality

/-! ## KernelComparisonComponents（旧 SerrePositivity/DifferentialGraded/Morita/KernelComparisonComponents.lean） -/

/-! # 通常kernel代表上の主作用比較の成分

## 概要
指定した標準局所化の通常代表では、主作用と既存作用の比較成分を恒等射として計算する。

## 方針
元の比較を定義するeqToIsoの成分を計算し、通常kernel射での作用も同じ計算へ接続する。

## 規約と注意
比較の定義は変えない。局所Hom K-flat性やkernelの射影性は不要。

## 使われ方
U16aの計算モデルのcoherenceを公開比較へ移す際の同じ代表上の簡約。
-/

@[expose] public section KernelComparisonComponents

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 通常代表上の公開比較同型は同じ作用の恒等比較。 -/
lemma kernelDerivedTensorOnBimoduleIso_refl (P : BimoduleCategory A E D) :
    kernelDerivedTensorOnBimoduleIso A D E P =
      Iso.refl (kernelDerivedTensorOnBimodule A D E (BimoduleCategory.underlying A E D P)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [kernelDerivedTensorOnBimoduleIso, Iso.app_hom, eqToIso.hom, eqToHom_app,
    Iso.refl_hom, NatTrans.id_app]
  rfl

/-- 通常kernel射の主作用は元の入力解像度作用の射そのもの。 -/
lemma kernelDerivedTensorFunctor_map_base {P P' : BimoduleCategory A E D} (f : P ⟶ P') :
    (kernelDerivedTensorFunctor A D E).map ((bimoduleToDerived A E D).map f) =
      kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D) f := by
  have h := kernelDerivedTensorOnBimoduleIso_naturality A D E f
  rw [kernelDerivedTensorOnBimoduleIso_refl, kernelDerivedTensorOnBimoduleIso_refl] at h
  simp only [Iso.refl_hom] at h
  erw [Category.comp_id, Category.id_comp] at h
  exact h

end SerrePositivity.DifferentialGraded.Morita
end

end KernelComparisonComponents
