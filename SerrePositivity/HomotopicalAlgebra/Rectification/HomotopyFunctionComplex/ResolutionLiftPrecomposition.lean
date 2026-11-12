module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.LiftSpacePrecomposition
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionLiftPostcomposition
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SourceInvariance
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionCategoryHom

/-!
# 中断した任意モデル源への一般化：ResolutionLiftPrecomposition

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Source change for higher resolution-lift families。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0309][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0309
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Source change for higher resolution-lift families

An actual lift between the outer frames induces source change of lift
spaces and a map between the same Kan target family. Outer frame lifts
are constructed by ordinary model factorization, with no functorial
source factorization assumption or assertion about chosen compositions.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionLiftPrecomposition
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev outer (X : ResolutionObject C) : ResolutionObject (SimplexCategory ⥤ C) :=
  ⟨X.resolution.obj, ResolutionLiftSpace.frame X⟩

abbrev FrameMap {X Y : ResolutionObject C} (f : X ⟶ Y) : Type v :=
  {φ : (ResolutionLiftSpace.frame X).obj ⟶ (ResolutionLiftSpace.frame Y).obj //
    φ ≫ (ResolutionLiftSpace.frame Y).augmentation =
      (ResolutionLiftSpace.frame X).augmentation ≫ (Functor.const SimplexCategory).map f.diagram}

def identity (X : ResolutionObject C) : FrameMap (𝟙 X) := ⟨𝟙 _, by
  change (𝟙 _) ≫ _ = _ ≫ (Functor.const SimplexCategory).map (𝟙 X.resolution.obj)
  rw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]⟩

def compose {X Y W : ResolutionObject C} {f : X ⟶ Y} {g : Y ⟶ W}
    (φ : FrameMap f) (ψ : FrameMap g) : FrameMap (f ≫ g) :=
  ⟨φ.val ≫ ψ.val, by
    rw [Category.assoc, ψ.property, ← Category.assoc, φ.property]
    change (_ ≫ _) ≫ _ = _ ≫ (Functor.const SimplexCategory).map (f.diagram ≫ g.diagram)
    rw [Functor.map_comp, Category.assoc]⟩

/-- An actual outer lift, constructed without a source factorization functor. -/
def lift {X Y : ResolutionObject C} (f : X ⟶ Y) : FrameMap f :=
  ⟨(ResolutionObject.lift f.diagram : outer X ⟶ outer Y).diagram,
    (ResolutionObject.lift f.diagram : outer X ⟶ outer Y).over⟩

def map (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) (φ : FrameMap f) :
    ResolutionLiftSpace.obj Y W g ⟶ ResolutionLiftSpace.obj X W (f.base ≫ g) :=
  LiftSpacePrecomposition.map (ResolutionLiftSpace.frame X).obj
    (ResolutionLiftSpace.frame Y).obj (ResolutionLiftSpace.frame X).augmentation
    (ResolutionLiftSpace.frame Y).augmentation f.diagram φ.val φ.property W.resolution.augmentation
    (ResolutionLiftSpace.baseMap X W (f.base ≫ g)) (ResolutionLiftSpace.baseMap Y W g) (by
      change f.diagram ≫ (Y.resolution.augmentation ≫ (Functor.const SimplexCategory).map g) =
        X.resolution.augmentation ≫ (Functor.const SimplexCategory).map (f.base ≫ g)
      rw [← Category.assoc, f.over, Category.assoc, Functor.map_comp])

lemma ofLift {X Y W : ResolutionObject C} (f : X ⟶ Y) (k : Y ⟶ W) (φ : FrameMap f) :
    ResolutionLiftSpace.ofLift k ≫ map X Y W f k.base φ = ResolutionLiftSpace.ofLift (f ≫ k) :=
  LiftSpacePrecomposition.ofLift _ _ _ _ f.diagram φ.val φ.property _ _ _ _ k.diagram k.over

abbrev rawTargetMap {X Y : ResolutionObject C} (f : X ⟶ Y) (φ : FrameMap f) (Z : C) :
    ResolutionLiftAction.target Y Z ⟶ ResolutionLiftAction.target X Z :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (DiagonalFrame.map φ.val)).app Z

lemma raw_comparison {X Y : ResolutionObject C} (f : X ⟶ Y) (φ : FrameMap f) (Z : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap f.diagram).app Z ≫ ResolutionLiftAction.comparison X Z =
      ResolutionLiftAction.comparison Y Z ≫ rawTargetMap f φ Z := by
  ext n x
  have h := congr_app (congr_app φ.property n.unop) n.unop
  change (φ.val.app n.unop).app n.unop ≫
      ((ResolutionLiftSpace.frame Y).augmentation.app n.unop).app n.unop =
    ((ResolutionLiftSpace.frame X).augmentation.app n.unop).app n.unop ≫ f.diagram.app n.unop at h
  change ((ResolutionLiftSpace.frame X).augmentation.app n.unop).app n.unop ≫
      (f.diagram.app n.unop ≫ x) =
    (φ.val.app n.unop).app n.unop ≫
      (((ResolutionLiftSpace.frame Y).augmentation.app n.unop).app n.unop ≫ x)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ x) h).symm.trans (Category.assoc _ _ _))

lemma raw_action (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : FrameMap f) (Z : C) {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj Y W g)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom W.resolution.obj).obj Z) :
    ResolutionLiftAction.parameterized X W (f.base ≫ g) Z (s ≫ map X Y W f g φ) t =
      ResolutionLiftAction.parameterized Y W g Z s t ≫ rawTargetMap f φ Z := by
  change DiagonalHom.pairing _ _ _ ((_ ≫ LiftSpacePrecomposition.map _ _ _ _ _ _ _ _ _ _ _) ≫ _)
      t = DiagonalHom.pairing _ _ _ (_ ≫ _) t ≫ _
  rw [Category.assoc, LiftSpacePrecomposition.map_inclusion, ← Category.assoc]
  exact DiagonalHom.pairing_source_naturality _ _ _ φ.val _ _

lemma boundary (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : FrameMap f) {K L : SSet.{v}} (i : K ⟶ L)
    (b : K ⟶ ResolutionLiftSpace.obj Y W g) (e : L ⟶ ResolutionLiftSpace.obj Y W g)
    (he : i ≫ e = b) :
    i ≫ (e ≫ map X Y W f g φ) = b ≫ map X Y W f g φ := by rw [← Category.assoc, he]

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- An actual map between the existing Kan target objects, without changing their models. -/
abbrev kanTargetMap {X Y : ResolutionObject C} (f : X ⟶ Y) (φ : FrameMap f) (Z : C) :
    KanLiftAction.target hcof hfib Y Z ⟶ KanLiftAction.target hcof hfib X Z :=
  (SimplicialModel.KanReplacement.functor hcof hfib).map (rawTargetMap f φ Z)

/-- Source change is a natural transformation of the existing target functors. -/
abbrev kanTargetNatTrans {X Y : ResolutionObject C} (f : X ⟶ Y) (φ : FrameMap f) :
    KanLiftAction.targetFunctor hcof hfib Y ⟶ KanLiftAction.targetFunctor hcof hfib X :=
  Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (DiagonalFrame.map φ.val))
    (SimplicialModel.KanReplacement.functor hcof hfib)

lemma kanTargetMap_identity (X : ResolutionObject C) (Z : C) :
    kanTargetMap hcof hfib (𝟙 X) (identity X) Z = 𝟙 _ := by
  have hd : DiagonalFrame.map (identity X).val = 𝟙 _ := by ext n; rfl
  have hh : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (𝟙 (DiagonalFrame.obj (ResolutionLiftSpace.frame X).obj))).app Z =
      𝟙 _ := by
    ext n x
    exact Category.id_comp x
  change (SimplicialModel.KanReplacement.functor hcof hfib).map _ = _
  rw [rawTargetMap, hd, hh, CategoryTheory.Functor.map_id]

lemma kanTargetMap_compose {X Y W : ResolutionObject C} (f : X ⟶ Y) (g : Y ⟶ W)
    (φ : FrameMap f) (ψ : FrameMap g) (Z : C) :
    kanTargetMap hcof hfib (f ≫ g) (compose φ ψ) Z =
      kanTargetMap hcof hfib g ψ Z ≫ kanTargetMap hcof hfib f φ Z := by
  have hd : DiagonalFrame.map (compose φ ψ).val =
      DiagonalFrame.map φ.val ≫ DiagonalFrame.map ψ.val := by ext n; rfl
  have hh : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (DiagonalFrame.map φ.val ≫ DiagonalFrame.map ψ.val)).app Z =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (DiagonalFrame.map ψ.val)).app Z ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (DiagonalFrame.map φ.val)).app Z := by
    ext n x
    exact Category.assoc _ _ _
  change (SimplicialModel.KanReplacement.functor hcof hfib).map _ =
    (SimplicialModel.KanReplacement.functor hcof hfib).map _ ≫
      (SimplicialModel.KanReplacement.functor hcof hfib).map _
  rw [rawTargetMap, hd, hh, Functor.map_comp]

lemma kan_comparison {X Y : ResolutionObject C} (f : X ⟶ Y) (φ : FrameMap f) (Z : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap f.diagram).app Z ≫ KanLiftAction.comparison hcof hfib X Z =
      KanLiftAction.comparison hcof hfib Y Z ≫ kanTargetMap hcof hfib f φ Z := by
  have hu := (SimplicialModel.KanReplacement.unit hcof hfib).naturality (rawTargetMap f φ Z)
  change rawTargetMap f φ Z ≫ (SimplicialModel.KanReplacement.unit hcof hfib).app
      (ResolutionLiftAction.target X Z) =
    (SimplicialModel.KanReplacement.unit hcof hfib).app (ResolutionLiftAction.target Y Z) ≫
      kanTargetMap hcof hfib f φ Z at hu
  change _ ≫ (ResolutionLiftAction.comparison X Z ≫ _) =
    (ResolutionLiftAction.comparison Y Z ≫ _) ≫ _
  rw [← Category.assoc, raw_comparison, Category.assoc, hu, ← Category.assoc]

lemma kanTargetMap_weakEquivalence {X Y : ResolutionObject C} (f : X ⟶ Y) (φ : FrameMap f)
    (hf : weakEquivalences C f.base) (Z : C) [IsFibrant Z] :
    weakEquivalences SSet.{v} (kanTargetMap hcof hfib f φ Z) := by
  have hw := cosimplicialHomMap_weakEquivalence hcof f.diagram X.resolution.cofibrant
    Y.resolution.cofibrant (fun n => ResolutionObject.diagram_weakEquivalence f hf n) Z
  have hc := (weakEquivalences SSet.{v}).comp_mem _ _ hw
    (KanLiftAction.comparison_weakEquivalence hcof hfib X Z)
  exact (weakEquivalences SSet.{v}).of_precomp _ _
    (KanLiftAction.comparison_weakEquivalence hcof hfib Y Z)
    ((kan_comparison hcof hfib f φ Z) ▸ hc)

lemma piZero_comparison {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
    [Q.IsLocalization (weakEquivalences C)] (X : ResolutionObject C) (Z : C) [IsFibrant Z]
    (z : SSet.π₀ ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom X.resolution.obj).obj Z)) :
    KanLiftAction.piZeroLocalizationEquiv hcof hfib Q X Z
        (SSet.mapπ₀ (KanLiftAction.comparison hcof hfib X Z) z) =
      resolutionPiZeroLocalizationEquiv Q X.resolution Z z := by
  change resolutionPiZeroLocalizationEquiv Q X.resolution Z
    ((Equiv.ofBijective _ (KanLiftAction.comparison_piZero_bijective hcof hfib X Z)).symm
      ((Equiv.ofBijective _ (KanLiftAction.comparison_piZero_bijective hcof hfib X Z)) z)) = _
  rw [Equiv.symm_apply_apply]

/-- On components the actual Kan source map is precomposition in any ordinary localization. -/
lemma piZero_naturality_source {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
    [Q.IsLocalization (weakEquivalences C)] {X Y : ResolutionObject C} (f : X ⟶ Y)
    (φ : FrameMap f) (Z : C) [IsFibrant Z] (z : SSet.π₀ (KanLiftAction.target hcof hfib Y Z)) :
    KanLiftAction.piZeroLocalizationEquiv hcof hfib Q X Z
        (SSet.mapπ₀ (kanTargetMap hcof hfib f φ Z) z) =
      Q.map f.base ≫ KanLiftAction.piZeroLocalizationEquiv hcof hfib Q Y Z z := by
  obtain ⟨x, rfl⟩ := (KanLiftAction.comparison_piZero_bijective hcof hfib Y Z).surjective z
  have hc := (SSet.mapπ₀_comp_apply ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap f.diagram).app Z)
    (KanLiftAction.comparison hcof hfib X Z) x).symm.trans
      ((congrArg (fun k => SSet.mapπ₀ k x) (kan_comparison hcof hfib f φ Z)).trans
        (SSet.mapπ₀_comp_apply (KanLiftAction.comparison hcof hfib Y Z)
          (kanTargetMap hcof hfib f φ Z) x))
  rw [← hc, piZero_comparison, piZero_comparison]
  exact ResolutionObject.piZeroEquiv_naturality_source Q (Quiver.Hom.op f) (FibrantObject.mk Z) x

lemma kan_action (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : FrameMap f) (Z : C) {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj Y W g)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom W.resolution.obj).obj Z) :
    KanLiftAction.parameterized hcof hfib X W (f.base ≫ g) Z (s ≫ map X Y W f g φ) t =
      KanLiftAction.parameterized hcof hfib Y W g Z s t ≫ kanTargetMap hcof hfib f φ Z := by
  have hu := (SimplicialModel.KanReplacement.unit hcof hfib).naturality (rawTargetMap f φ Z)
  change rawTargetMap f φ Z ≫ (SimplicialModel.KanReplacement.unit hcof hfib).app
      (ResolutionLiftAction.target X Z) =
    (SimplicialModel.KanReplacement.unit hcof hfib).app (ResolutionLiftAction.target Y Z) ≫
      kanTargetMap hcof hfib f φ Z at hu
  change ResolutionLiftAction.parameterized X W (f.base ≫ g) Z (s ≫ map X Y W f g φ) t ≫ _ =
    (_ ≫ _) ≫ _
  rw [raw_action, Category.assoc, hu, ← Category.assoc]

end SerrePositivity.HomotopyFunctionComplex.ResolutionLiftPrecomposition
