module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionTensorComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorZero
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAugmentationModels
public import Mathlib.Algebra.Algebra.Tower

/-!
# 代数作用から得る完備導来テンソルの消滅
## 概要
A 加群 M の標準作用を使い、K⊗̂ᴸA=0 から K⊗̂ᴸM=0 を導く。
## 方針
M を A⊗ᴸM の retract とし、元の完備化同値の tensor 安定性と結合則を使う。
## 規約
任意の可換環と完備化元を許し、代数や加群の平坦性・有限性は要求しない。
## 使われ方
BS 著者版 Prop 10.4（印刷 p.79）の商加群に対する方向を供給する。
-/

@[expose] public noncomputable section
universe u
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
BS 著者版 Prop 10.4（印刷 p.79）の商加群の消滅に使う。
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
BS 著者版 Prop 10.4（印刷 p.79）の代数作用による消滅判定に使う。
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
BS 著者版 Prop 10.4（印刷 p.79）の商環上の加群に適用する。
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
BS 著者版 Prop 10.4（印刷 p.79）の商加群からの消滅を与える。
-/
theorem completedTensor_isZero_of_algebraModule (K : D)
    (hKA : IsZero ((derivedComplexCompletionFunctor R a).obj
      (K ⊗ boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)).obj)) :
    IsZero ((derivedComplexCompletionFunctor R a).obj
      (K ⊗ boundedAboveDerivedSingleFunctor.obj M).obj) := by
  obtain ⟨i, r, hi⟩ := derivedTensor_module_action_retract R A M
  exact completedTensor_isZero_of_action_retract R a K _ _ hKA i r hi

end SerrePositivity.DerivedCompletion
