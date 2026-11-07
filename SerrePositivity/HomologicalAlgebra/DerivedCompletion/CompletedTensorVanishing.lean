module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionMonoidal
public import SerrePositivity.HomologicalAlgebra.DerivedTensorLinear
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAugmentationModels
public import Mathlib.Algebra.Algebra.Tower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection
public import SerrePositivity.HomologicalAlgebra.BoundedAbove.Derived
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedBaseChange
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedModule
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import SerrePositivity.HomologicalAlgebra.DerivedTensorFixedModuleModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePower
public import SerrePositivity.HomologicalAlgebra.CompleteFaithfullyFlatDescent

/-! # 完備導来テンソルの消滅と完全三角形

## 概要

零の係数の完備化と完備テンソルが零であること、代数の作用の retract を使って `K ⊗̂ᴸ A = 0` から `K ⊗̂ᴸ M = 0` を導くこと（BS 著者版 Proposition 10.4 の商加群の向き）、完備導来基底変更の完全三角形、加群の短完全列の完備導来基底変更、短完全列に固定加群を完備テンソルした射の零判定（BS 著者版 Lemma 10.3 の混合積）を与える。加群の写像の錐の完備基底変更の完全三角形と錐の比較（`completedModuleConeIso`、旧 CLMST の Prop 2.4.7 の証明の一般部分）も与える。
完備導来テンソルによる消滅の拡大閉性は、BS 著者版 Proposition 10.2 の証明に使う一般補題である。

## 方針

元の完備化同値のテンソル安定性と結合則、固定係数の射影分解の模型の自然性を使う。

## 規約

任意の可換環と完備化の元を許し、平坦性・有限性は要らない。旧 `CompletedTensorZero`・`CompletedTensorModuleAction`・`CompletedBaseChangeTriangle`・`CompletedModuleShortExact`・`CompletedTensorShortExact`。

## 使われ方

BhattScholze の Almost、CLMST。
-/

@[expose] public noncomputable section

universe u

section CompletedTensorZeroPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- The original completion of a zero derived object is zero. -/
lemma derivedCompletion_isZero_of_isZero (a : R) (X : ConcreteDerivedCategory R)
    (hX : IsZero X) : IsZero ((derivedComplexCompletionFunctor R a).obj X) := by
  have hc : IsComplete R a X := isComplete_of_scalar_pow_zero R a X 1 (hX.eq_of_src _ _)
  exact hX.of_iso (derivedComplexCompletionUnitIso R a X hc).symm

/-- The actual bounded single object of a zero module is zero. -/
lemma boundedAboveDerivedSingle_isZero (M : ModuleCat.{u} R) (hM : IsZero M) :
    IsZero (boundedAboveDerivedSingleFunctor.obj M) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply InducedCategory.hom_ext
  exact ((DerivedCategory.singleFunctor (ModuleCat R) 0).map_isZero hM).eq_of_src _ _

/-- A zero left coefficient gives a zero original completed tensor. -/
lemma completedTensor_isZero_of_left_isZero (a : R) (M N : ModuleCat.{u} R)
    (hM : IsZero M) :
    IsZero (((boundedAboveDerivedCompletionFunctor R a).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N)))).obj := by
  have hz := (tensorRight (boundedAboveDerivedSingleFunctor.obj N)).map_isZero
    (boundedAboveDerivedSingle_isZero R M hM)
  have hz' := DerivedCategory.Minus.ι.map_isZero hz
  exact derivedCompletion_isZero_of_isZero R a _ hz'

/-- A zero right coefficient gives a zero original completed tensor as well. -/
lemma completedTensor_isZero_of_right_isZero (a : R) (M N : ModuleCat.{u} R)
    (hN : IsZero N) :
    IsZero (((boundedAboveDerivedCompletionFunctor R a).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N)))).obj := by
  have hz := (tensorLeft (boundedAboveDerivedSingleFunctor.obj M)).map_isZero
    (boundedAboveDerivedSingle_isZero R N hN)
  have hz' := DerivedCategory.Minus.ι.map_isZero hz
  exact derivedCompletion_isZero_of_isZero R a _ hz'

end SerrePositivity.DerivedCompletion

end CompletedTensorZeroPart

section CompletedTensorModuleActionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/--
## 概要
完備化後に零となる対象を任意の上有界対象とテンソルしても、完備化後に零となる。
## 方針
零対象への射は完備化同値なので、既存の右 tensor による安定性を使う。
## 規約
元の導来テンソルと完備化を使う。
## 使われ方
BS 著者版 Proposition 10.4（印刷 p.79）の商加群の消滅に使う。
-/
theorem completedTensor_isZero_whiskerRight (X Y : D)
    (hX : IsZero ((derivedComplexCompletionFunctor R a).obj X.obj)) :
    IsZero ((derivedComplexCompletionFunctor R a).obj (X ⊗ Y).obj) := by
  let F := derivedComplexCompletionFunctor R a
  let Z := boundedAboveDerivedSingleFunctor.obj (0 : ModuleCat.{u} R)
  have hZ : IsZero Z := boundedAboveDerivedSingle_isZero R _ (isZero_zero _)
  let f : X ⟶ Z := 0
  have h0 : IsZero (F.obj Z.obj) := derivedCompletion_isZero_of_isZero R a _
    ((DerivedCategory.Minus.ι (C := ModuleCat R)).map_isZero hZ)
  have hf : IsIso (F.map f.hom) := hX.isIso h0 _
  have := completionEquivalence_whiskerRight R a f hf Y
  have hz : IsZero (F.obj (Z ⊗ Y).obj) := derivedCompletion_isZero_of_isZero R a _
    ((DerivedCategory.Minus.ι (C := ModuleCat R)).map_isZero
      ((tensorRight Y).map_isZero hZ))
  exact hz.of_iso (asIso (F.map (f ▷ Y).hom))

/--
## 概要
M が A⊗ᴸM の retract であり K⊗̂ᴸA が零なら、K⊗̂ᴸM も零となる。
## 方針
結合則と tensor 安定性で K⊗̂ᴸ(A⊗ᴸM) を零にし、retract の恒等式を移す。
## 規約
retract の射と恒等式を明示的に受け取る。
## 使われ方
BS 著者版 Proposition 10.4（印刷 p.79）の代数作用による消滅判定に使う。
-/
theorem completedTensor_isZero_of_action_retract (K A M : D)
    (hKA : IsZero ((derivedComplexCompletionFunctor R a).obj (K ⊗ A).obj))
    (i : M ⟶ A ⊗ M) (r : A ⊗ M ⟶ M) (hi : i ≫ r = 𝟙 M) :
    IsZero ((derivedComplexCompletionFunctor R a).obj (K ⊗ M).obj) := by
  let F := derivedComplexCompletionFunctor R a
  let G := tensorLeft K ⋙ DerivedCategory.Minus.ι ⋙ F
  have hz : IsZero (G.obj (A ⊗ M)) :=
    (completedTensor_isZero_whiskerRight R a (K ⊗ A) M hKA).of_iso
      (F.mapIso (DerivedCategory.Minus.ι.mapIso (α_ K A M))).symm
  have hcomp : G.map i ≫ G.map r = 𝟙 (G.obj M) := by
    rw [← CategoryTheory.Functor.map_comp, hi, CategoryTheory.Functor.map_id]
  change IsZero (G.obj M)
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← hcomp, hz.eq_of_tgt (G.map i) 0, zero_comp]

variable (A : Type u) [CommRing A] [Algebra R A]
variable (M : ModuleCat.{u} R) [Module A M] [IsScalarTower R A M]

/--
## 概要
R 代数 A 上の加群 M は、元の導来テンソル A⊗ᴸ_R M の retract になる。
## 方針
代数単位を左に tensor した射と、既存導来増大射に通常の作用を合成した射を用いる。
## 規約
加群構造のスカラー塔を明示し、導来単位則と元の作用を照合する。
## 使われ方
BS 著者版 Proposition 10.4（印刷 p.79）の商環上の加群に適用する。
-/
theorem derivedTensor_module_action_retract :
    ∃ (i : boundedAboveDerivedSingleFunctor.obj M ⟶
        boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A),
            boundedAboveDerivedSingleFunctor.obj M))
      (r : boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A),
            boundedAboveDerivedSingleFunctor.obj M) ⟶ boundedAboveDerivedSingleFunctor.obj M),
      i ≫ r = 𝟙 _ := by
  let q : ModuleCat.of R R ⟶ ModuleCat.of R A := ModuleCat.ofHom (Algebra.linearMap R A)
  let act : (ModuleCat.of R A) ⊗ M ⟶ M :=
    ModuleCat.ofHom (TensorProduct.lift (Algebra.lsmul R R M).toLinearMap)
  let t := boundedAboveDerivedTensor.map
    (CategoryTheory.Prod.mkHom (boundedAboveDerivedSingleFunctor.map q)
      (𝟙 (boundedAboveDerivedSingleFunctor.obj M)))
  let l := boundedAboveDerivedTensorLeftUnitor (boundedAboveDerivedSingleFunctor.obj M)
  let r : boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A),
        boundedAboveDerivedSingleFunctor.obj M) ⟶ boundedAboveDerivedSingleFunctor.obj M :=
    ObjectProperty.homMk ((boundedAboveDerivedTensorModuleAugmentation
      (ModuleCat.of R A)).app M ≫ (DerivedCategory.singleFunctor (ModuleCat R) 0).map act)
  refine ⟨l.inv ≫ t, r, ?_⟩
  have he : (((tensoringLeft (ModuleCat R)).map q).app M) ≫ act = (λ_ M).hom := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x m
    change (algebraMap R A x) • m = x • m
    exact IsScalarTower.algebraMap_smul A x m
  apply InducedCategory.hom_ext
  change (l.inv.hom ≫ t.hom) ≫
    ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app M ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map act) = 𝟙 _
  rw [Category.assoc]
  rw [← Category.assoc t.hom, boundedAboveDerivedTensorModuleAugmentation_naturality_left,
    Category.assoc, ← Functor.map_comp, he,
    boundedAboveDerivedTensorModuleAugmentation_leftUnitor]
  exact congrArg (fun f => f.hom) l.inv_hom_id

/--
## 概要
K⊗̂ᴸA が零なら、任意の A 加群 M に対して K⊗̂ᴸM は零である。
## 方針
標準代数作用から得た retract に、結合則と完備化同値の tensor 安定性を適用する。
## 規約
M の完備性・平坦性・有限性は必要ない。
## 使われ方
BS 著者版 Proposition 10.4（印刷 p.79）の商加群からの消滅を与える。
-/
theorem completedTensor_isZero_of_algebraModule (K : D)
    (hKA : IsZero ((derivedComplexCompletionFunctor R a).obj
      (K ⊗ boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)).obj)) :
    IsZero ((derivedComplexCompletionFunctor R a).obj
      (K ⊗ boundedAboveDerivedSingleFunctor.obj M).obj) := by
  obtain ⟨i, r, hi⟩ := derivedTensor_module_action_retract R A M
  exact completedTensor_isZero_of_action_retract R a K _ _ hKA i r hi

end SerrePositivity.DerivedCompletion

end CompletedTensorModuleActionPart

section CompletedBaseChangeTrianglePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B) (a : R)
variable {X Y Z : DerivedCategory.Minus (ModuleCat.{u} R)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (δ : Z ⟶ X⟦(1 : ℤ)⟧)

/-- 元の全ての射を用いた、完備導来底変換後の三角形。 -/
def completedBaseChangeTriangle : Triangle (ConcreteDerivedCategory B) :=
  (derivedComplexCompletionFunctor B (φ a)).mapTriangle.obj
    (boundedAboveLeftDerivedTriangle (ModuleCat.extendScalars φ) f g δ)

/-- 実完全三角形の完備導来底変換は実完全三角形。 -/
theorem completedBaseChangeTriangle_distinguished
    (hT : Triangle.mk f.hom g.hom
      (δ.hom ≫ (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app X) ∈
        distTriang (ConcreteDerivedCategory R)) :
    completedBaseChangeTriangle φ a f g δ ∈ distTriang (ConcreteDerivedCategory B) :=
  (derivedComplexCompletionFunctor B (φ a)).map_distinguished _
    (boundedAboveLeftDerivedTriangle_distinguished (ModuleCat.extendScalars φ) f g δ hT)

end SerrePositivity.DerivedCompletion

end CompletedBaseChangeTrianglePart

section CompletedModuleShortExactPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B) (a : R)

/-- 元の加群の短完全列から、実完備導来底変換の三角形を作る。 -/
def completedModuleShortExactTriangle (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    Triangle (ConcreteDerivedCategory B) :=
  let T := DerivedCategory.triangleOfSES
    (hS.map_of_exact (CochainComplex.singleFunctor (ModuleCat R) 0))
  let X := boundedAboveDerivedSingleFunctor.obj S.X₁
  let Y := boundedAboveDerivedSingleFunctor.obj S.X₂
  let Z := boundedAboveDerivedSingleFunctor.obj S.X₃
  let f : X ⟶ Y := ObjectProperty.homMk T.mor₁
  let g : Y ⟶ Z := ObjectProperty.homMk T.mor₂
  let δ : Z ⟶ X⟦(1 : ℤ)⟧ := ObjectProperty.homMk
    (T.mor₃ ≫ (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).inv.app X)
  completedBaseChangeTriangle φ a f g δ

/-- 短完全列の三項の実完備底変換は完全三角形をなす。 -/
theorem completedModuleShortExactTriangle_distinguished
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    completedModuleShortExactTriangle φ a S hS ∈ distTriang (ConcreteDerivedCategory B) := by
  unfold completedModuleShortExactTriangle
  apply completedBaseChangeTriangle_distinguished
  simp only [ObjectProperty.homMk_hom, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact DerivedCategory.triangleOfSES_distinguished
    (hS.map_of_exact (CochainComplex.singleFunctor (ModuleCat R) 0))

/-- 短完全列の両端の完備底変換が離散なら、中央も離散。 -/
theorem completedBaseChangeModule_shortExact_pure
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (h₁ :
      let Y := (derivedComplexCompletionFunctor B (φ a)).obj
        ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj S.X₁)).obj
      Y.IsGE 0 ∧ Y.IsLE 0)
    (h₃ :
      let Y := (derivedComplexCompletionFunctor B (φ a)).obj
        ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj S.X₃)).obj
      Y.IsGE 0 ∧ Y.IsLE 0) :
    let Y := (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj S.X₂)).obj
    Y.IsGE 0 ∧ Y.IsLE 0 := by
  let T := completedModuleShortExactTriangle φ a S hS
  have hd := completedModuleShortExactTriangle_distinguished φ a S hS
  exact ⟨DerivedCategory.TStructure.t.isGE₂ T hd 0 h₁.1 h₃.1,
    DerivedCategory.TStructure.t.isLE₂ T hd 0 h₁.2 h₃.2⟩

end SerrePositivity.DerivedCompletion

end CompletedModuleShortExactPart

section CompletedTensorShortExactPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R) (C : ModuleCat.{u} R)

/--
## 概要
短完全列の完備導来テンソルの第二射が同型なら、第一対象は零である。
## 方針
固定射影分解との自然同型で完全三角形へ移し、第二射の同型性から結論する。
## 規約
仮定の射は元の導来テンソル関手による実射である。
## 使われ方
BS 著者版 Lemma 10.3（著者版 pp.78–79）の核と商の混合積の消滅を導く。
-/
theorem completedTensor_isZero_of_shortExact_rightMap_isIso
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hg : IsIso ((derivedComplexCompletionFunctor R a).map
      ((boundedAboveDerivedTensorModuleFunctor C).map S.g))) :
    IsZero ((derivedComplexCompletionFunctor R a).obj
      ((boundedAboveDerivedTensorModuleFunctor C).obj S.X₁)) := by
  let F := derivedComplexCompletionFunctor R a
  let K := extRes (projectiveResolution C)
  have hs := moduleTensorCochain_shortExact K (moduleCoefficientResolution_flat C) S hS
  let T := F.mapTriangle.obj (DerivedCategory.triangleOfSES hs)
  have hd : T ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.triangleOfSES_distinguished hs)
  let e₂ := F.mapIso (derivedTensorCoefficientModelIso C S.X₂)
  let e₃ := F.mapIso (derivedTensorCoefficientModelIso C S.X₃)
  have hn : F.map ((boundedAboveDerivedTensorModuleFunctor C).map S.g) ≫ e₃.hom =
      e₂.hom ≫ T.mor₂ := by
    exact (by simpa [Functor.map_comp, Functor.mapIso_hom, e₂, e₃, T,
      DerivedCategory.triangleOfSES] using
      congrArg F.map (derivedTensorCoefficientModelIso_naturality C S.g))
  have : IsIso (e₂.hom ≫ T.mor₂) := by rw [← hn]; infer_instance
  have : IsIso T.mor₂ := IsIso.of_isIso_comp_left e₂.hom T.mor₂
  exact (T.isZero₁_of_isIso₂ hd inferInstance).of_iso
    (F.mapIso (derivedTensorCoefficientModelIso C S.X₁))

/--
## 概要
短完全列の完備導来テンソルの第三対象が零なら、第一射は同型である。
## 方針
固定係数の自然な射影分解モデルの完全三角形で判定し、元の実射へ戻す。
## 規約
第三対象の消滅をホモロジーの一部の消滅で代用しない。
## 使われ方
BS 著者版 Lemma 10.3（著者版 pp.78–79）の核の自己積に使う。
-/
theorem completedTensor_shortExact_leftMap_isIso_of_isZero
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hz : IsZero ((derivedComplexCompletionFunctor R a).obj
      ((boundedAboveDerivedTensorModuleFunctor C).obj S.X₃))) :
    IsIso ((derivedComplexCompletionFunctor R a).map
      ((boundedAboveDerivedTensorModuleFunctor C).map S.f)) := by
  let F := derivedComplexCompletionFunctor R a
  let K := extRes (projectiveResolution C)
  have hs := moduleTensorCochain_shortExact K (moduleCoefficientResolution_flat C) S hS
  let T := F.mapTriangle.obj (DerivedCategory.triangleOfSES hs)
  have hd : T ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.triangleOfSES_distinguished hs)
  have hz' : IsZero T.obj₃ := hz.of_iso
    (F.mapIso (derivedTensorCoefficientModelIso C S.X₃)).symm
  have : IsIso T.mor₁ := (T.isZero₃_iff_isIso₁ hd).mp hz'
  let e₁ := F.mapIso (derivedTensorCoefficientModelIso C S.X₁)
  let e₂ := F.mapIso (derivedTensorCoefficientModelIso C S.X₂)
  have hn : F.map ((boundedAboveDerivedTensorModuleFunctor C).map S.f) ≫ e₂.hom =
      e₁.hom ≫ T.mor₁ := by
    exact (by simpa [Functor.map_comp, Functor.mapIso_hom, e₁, e₂, T,
      DerivedCategory.triangleOfSES] using
      congrArg F.map (derivedTensorCoefficientModelIso_naturality C S.f))
  have : IsIso (F.map ((boundedAboveDerivedTensorModuleFunctor C).map S.f) ≫ e₂.hom) := by
    rw [hn]; infer_instance
  exact IsIso.of_isIso_comp_right
    (F.map ((boundedAboveDerivedTensorModuleFunctor C).map S.f)) e₂.hom

/--
## 概要
短完全列の完備導来テンソルの第一対象が零なら、第二射は同型である。
## 方針
固定射影分解モデルの完全三角形で判定し、既存の自然同型で実射へ戻す。
## 規約
完備性・平坦性の追加仮定は置かない。
## 使われ方
BS 著者版 Proposition 10.4（印刷 p.79）の商作用を復元する方向に使う。
-/
theorem completedTensor_shortExact_rightMap_isIso_of_isZero
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hz : IsZero ((derivedComplexCompletionFunctor R a).obj
      ((boundedAboveDerivedTensorModuleFunctor C).obj S.X₁))) :
    IsIso ((derivedComplexCompletionFunctor R a).map
      ((boundedAboveDerivedTensorModuleFunctor C).map S.g)) := by
  let F := derivedComplexCompletionFunctor R a
  let K := extRes (projectiveResolution C)
  have hs := moduleTensorCochain_shortExact K (moduleCoefficientResolution_flat C) S hS
  let T := F.mapTriangle.obj (DerivedCategory.triangleOfSES hs)
  have hd : T ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.triangleOfSES_distinguished hs)
  have hz' : IsZero T.obj₁ := hz.of_iso
    (F.mapIso (derivedTensorCoefficientModelIso C S.X₁)).symm
  have : IsIso T.mor₂ := (T.isZero₁_iff_isIso₂ hd).mp hz'
  let e₂ := F.mapIso (derivedTensorCoefficientModelIso C S.X₂)
  let e₃ := F.mapIso (derivedTensorCoefficientModelIso C S.X₃)
  have hn : F.map ((boundedAboveDerivedTensorModuleFunctor C).map S.g) ≫ e₃.hom =
      e₂.hom ≫ T.mor₂ := by
    simpa [Functor.map_comp, e₂, e₃, T, DerivedCategory.triangleOfSES] using
      congrArg F.map (derivedTensorCoefficientModelIso_naturality C S.g)
  have : IsIso (F.map ((boundedAboveDerivedTensorModuleFunctor C).map S.g) ≫ e₃.hom) := by
    rw [hn]; infer_instance
  exact IsIso.of_isIso_comp_right _ e₃.hom

/--
## 概要
短完全列の両端の完備導来テンソルが零なら、中央の完備導来テンソルも零である。
## 方針
同じ固定射影分解モデルの完全三角形で、両端の零対象性を用いる。
## 規約
元の短完全列に適用し、加群の通常の tensor 完全性は仮定しない。
## 使われ方
完備 almost 零加群の拡大閉性に使う。
-/
theorem completedTensor_isZero_of_shortExact
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (h₁ : IsZero ((derivedComplexCompletionFunctor R a).obj
      ((boundedAboveDerivedTensorModuleFunctor C).obj S.X₁)))
    (h₃ : IsZero ((derivedComplexCompletionFunctor R a).obj
      ((boundedAboveDerivedTensorModuleFunctor C).obj S.X₃))) :
    IsZero ((derivedComplexCompletionFunctor R a).obj
      ((boundedAboveDerivedTensorModuleFunctor C).obj S.X₂)) := by
  let F := derivedComplexCompletionFunctor R a
  let K := extRes (projectiveResolution C)
  have hs := moduleTensorCochain_shortExact K (moduleCoefficientResolution_flat C) S hS
  let T := F.mapTriangle.obj (DerivedCategory.triangleOfSES hs)
  have hd : T ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.triangleOfSES_distinguished hs)
  have hz₁ : IsZero T.obj₁ := h₁.of_iso
    (F.mapIso (derivedTensorCoefficientModelIso C S.X₁)).symm
  have hz₃ : IsZero T.obj₃ := h₃.of_iso
    (F.mapIso (derivedTensorCoefficientModelIso C S.X₃)).symm
  exact (T.isZero₂_of_isZero₁₃ hd hz₁ hz₃).of_iso
    (F.mapIso (derivedTensorCoefficientModelIso C S.X₂))

end SerrePositivity.DerivedCompletion

end CompletedTensorShortExactPart

section ModuleMapConeComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Pretriangulated DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B) (a : R)
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- 元の加群写像の標準三角形に対する実完備導来底変換。 -/
def completedModuleTriangle (f : M →ₗ[R] N) : Triangle (ConcreteDerivedCategory B) :=
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R M)
  let Y := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R N)
  let C := moduleMapConeBoundedAbove f
  let u : X ⟶ Y := boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f)
  let v : Y ⟶ C := ObjectProperty.homMk (moduleMapConeTriangle R f).mor₂
  let δ : C ⟶ X⟦(1 : ℤ)⟧ := ObjectProperty.homMk
    ((moduleMapConeTriangle R f).mor₃ ≫
      (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).inv.app X)
  completedBaseChangeTriangle φ a u v δ

/-- 元の実加群写像の錐は、完備導来底変換後も実完全三角形の第三対象となる。 -/
theorem completedModuleTriangle_distinguished (f : M →ₗ[R] N) :
    completedModuleTriangle φ a f ∈ distTriang (ConcreteDerivedCategory B) := by
  apply completedBaseChangeTriangle_distinguished
  simp only [ObjectProperty.homMk_hom, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  change moduleMapConeTriangle R f ∈ distTriang _
  exact moduleMapConeTriangle_distinguished R f

/-- 標準射の始域・終域の比較を、実完備底変換錐と実加群写像錐の比較へ延長する。 -/
def completedModuleConeIso
    {L P : Type u} [AddCommGroup L] [Module B L] [AddCommGroup P] [Module B P]
    (f : M →ₗ[R] N) (α : L →ₗ[B] P)
    (eM : (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R M))).obj ≅
      (moduleObjectFunctor B).obj (ModuleCat.of B L))
    (eN : (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R N))).obj ≅
      (moduleObjectFunctor B).obj (ModuleCat.of B P))
    (hsq : (derivedComplexCompletionFunctor B (φ a)).map
        ((boundedAboveDerivedBaseChange φ).map
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f))).hom ≫ eN.hom =
      eM.hom ≫ (moduleObjectFunctor B).map (ModuleCat.ofHom α)) :
    (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj (moduleMapConeBoundedAbove f)).obj ≅
        moduleMapCone B α :=
  Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _
    (completedModuleTriangle_distinguished φ a f)
    (moduleMapConeTriangle_distinguished B α) eM eN hsq)

/-- 第三対象の比較は、元の実三角形の標準の右包含を保つ。 -/
theorem completedModuleConeIso_inclusion
    {L P : Type u} [AddCommGroup L] [Module B L] [AddCommGroup P] [Module B P]
    (f : M →ₗ[R] N) (α : L →ₗ[B] P)
    (eM : (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R M))).obj ≅
      (moduleObjectFunctor B).obj (ModuleCat.of B L))
    (eN : (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R N))).obj ≅
      (moduleObjectFunctor B).obj (ModuleCat.of B P))
    (hsq : (derivedComplexCompletionFunctor B (φ a)).map
        ((boundedAboveDerivedBaseChange φ).map
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f))).hom ≫ eN.hom =
      eM.hom ≫ (moduleObjectFunctor B).map (ModuleCat.ofHom α)) :
    (completedModuleTriangle φ a f).mor₂ ≫
        (completedModuleConeIso φ a f α eM eN hsq).hom =
      eN.hom ≫ (moduleMapConeTriangle B α).mor₂ := by
  exact (isoTriangleOfIso₁₂ _ _
    (completedModuleTriangle_distinguished φ a f)
    (moduleMapConeTriangle_distinguished B α) eM eN hsq).hom.comm₂

end SerrePositivity.DerivedCompletion

end ModuleMapConeComparisonPart
