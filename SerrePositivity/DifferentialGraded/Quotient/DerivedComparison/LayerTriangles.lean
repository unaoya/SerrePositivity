module

public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.ColimitCones
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects
public import SerrePositivity.DifferentialGraded.Module.ConeDesc
public import SerrePositivity.DifferentialGraded.Derived.ConeTriangles
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import SerrePositivity.DifferentialGraded.Module.Ring
public import SerrePositivity.DifferentialGraded.Module.TensorAdjunction
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Module.RestrictionColimits
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentable
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
public import SerrePositivity.DifferentialGraded.Tensor.Parameter

/-!
# Quotient.DerivedComparison.LayerTriangles

## 概要
長さ層の加群・三角形と自由加群の導来延長をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w

/-! ## DerivedComparisonLayerModule（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonLayerModule.lean） -/

/-! # 長さ filtration の層射影を右 dg 加群射にする -/

@[expose] public section DerivedComparisonLayerModule

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 層射影は、最終微分についての先頭作用を固定長の内部作用へ移す。 -/
lemma lengthLayerProjection_prepend (S : Set D) (x y z : D) (n : ℕ) :
    lengthPrepend A D S x y z (n + 1) ≫ lengthLayerProjection A D S x z n =
      (homObject A D x y ◁ lengthLayerProjection A D S y z n) ≫
        selectedPrepend A D S (fun w => w.length = n + 1) x y z := by
  apply tensorHom_ext
  intro p q r hr
  rw [HomologicalComplex.comp_f, ← Category.assoc, lengthPrepend_ι,
    HomologicalComplex.comp_f, ← Category.assoc, ι_whiskerLeft]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f t
  change (fixedLengthProjection A D S x z (n + 1)).f r
      (lengthPrependComponent A D S x y z (n + 1) p q r hr (f ⊗ₜ[A] t)).val =
    (selectedPrepend A D S (fun w => w.length = n + 1) x y z).f r
      (ιTensorObj (homObject A D x y) (fixedLengthHom A D S y z (n + 1)) p q r hr
        (f ⊗ₜ[A] (fixedLengthProjection A D S y z (n + 1)).f q t.val))
  rw [lengthPrependComponent_coe]
  have h := congrArg (fun g => g.f r
    (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q r hr (f ⊗ₜ[A] t.val)))
      (selectedProjection_prepend A D S (fun w => w.length = n + 1) x y z)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
  rw [whiskerLeft_apply] at h
  exact h

/-- 固定長 path 加群へ値を移した層射影。 -/
def lengthLayerModuleComponent (S : Set D) (z : D) (n : ℕ) (x : Dᵒᵖ) :
    lengthComplex A D S x.unop z (n + 1) ⟶
      (moduleEvaluation A D x.unop).obj
        (selectedPathModule A D S (fun w => w.length = n + 1) z) :=
  lengthLayerProjection A D S x.unop z n ≫
    (selectedPathModuleEvaluationIso A D S (fun w => w.length = n + 1) z x).inv

@[reassoc] lemma lengthLayerModuleComponent_evaluation (S : Set D) (z : D) (n : ℕ)
    (x : Dᵒᵖ) :
    lengthLayerModuleComponent A D S z n x ≫
        (selectedPathModuleEvaluationIso A D S (fun w => w.length = n + 1) z x).hom =
      lengthLayerProjection A D S x.unop z n := by
  dsimp only [lengthLayerModuleComponent]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma lengthLayerModuleComponent_action (S : Set D) (z : D) (n : ℕ) (x y : Dᵒᵖ) :
    moduleActionChain A (lengthModule A D S z (n + 1)) x y ≫
        lengthLayerModuleComponent A D S z n y =
      ((x ⟶[Complex A] y) ◁ lengthLayerModuleComponent A D S z n x) ≫
        moduleActionChain A (ForgetEnrichment.to (Complex A)
          (selectedPathModule A D S (fun w => w.length = n + 1) z)) x y := by
  apply (cancel_mono
    (selectedPathModuleEvaluationIso A D S (fun w => w.length = n + 1) z y).hom).mp
  calc
    _ = lengthPrepend A D S y.unop x.unop z (n + 1) ≫
        lengthLayerProjection A D S y.unop z n := by
      rw [Category.assoc, lengthLayerModuleComponent_evaluation]
      change uncurryRight (curryRight (lengthPrepend A D S y.unop x.unop z (n + 1))) ≫ _ = _
      rw [uncurryRight_curryRight]
    _ = ((x ⟶[Complex A] y) ◁ lengthLayerProjection A D S x.unop z n) ≫
        selectedPrepend A D S (fun w => w.length = n + 1) y.unop x.unop z :=
      lengthLayerProjection_prepend A D S y.unop x.unop z n
    _ = _ := by
      have h := congrArg (fun f =>
        ((x ⟶[Complex A] y) ◁ lengthLayerModuleComponent A D S z n x) ≫ f)
          (selectedPathModuleEvaluationIso_action A D S (fun w => w.length = n + 1) z x y)
      simp only [← Category.assoc] at h
      rw [← MonoidalCategory.whiskerLeft_comp, lengthLayerModuleComponent_evaluation] at h
      exact h.symm

lemma lengthLayerModuleComponent_naturality (S : Set D) (z : D) (n : ℕ) (x y : Dᵒᵖ) :
    (lengthModule A D S z (n + 1)).map x y ≫
        homPostcompose (lengthComplex A D S x.unop z (n + 1))
          (lengthLayerModuleComponent A D S z n y) =
      (ForgetEnrichment.to (Complex A)
        (selectedPathModule A D S (fun w => w.length = n + 1) z)).map x y ≫
          homPrecompose (lengthLayerModuleComponent A D S z n x)
            ((moduleEvaluation A D y.unop).obj
              (selectedPathModule A D S (fun w => w.length = n + 1) z)) := by
  have h := congrArg curryRight (lengthLayerModuleComponent_action A D S z n x y)
  change curryRight (uncurryRight ((lengthModule A D S z (n + 1)).map x y) ≫
    lengthLayerModuleComponent A D S z n y) =
      curryRight ((𝟙 (x ⟶[Complex A] y) ⊗ₘ lengthLayerModuleComponent A D S z n x) ≫
        uncurryRight ((ForgetEnrichment.to (Complex A)
          (selectedPathModule A D S (fun w => w.length = n + 1) z)).map x y)) at h
  rw [curryRight_naturality_target, curryRight_naturality_domain,
    curryRight_uncurryRight, curryRight_uncurryRight] at h
  exact h

/-- 固定長部分への実際の全次数自然な右 dg 加群射。 -/
def lengthLayerModuleProjection (S : Set D) (z : D) (n : ℕ) :
    ForgetEnrichment.of (Complex A) (lengthModule A D S z (n + 1)) ⟶
      selectedPathModule A D S (fun w => w.length = n + 1) z :=
  moduleMorphismMk A D (lengthLayerModuleComponent A D S z n)
    (lengthLayerModuleComponent_naturality A D S z n)

@[simp] lemma lengthLayerModuleProjection_eval (S : Set D) (z : D) (n : ℕ) (x : D) :
    (moduleEvaluation A D x).map (lengthLayerModuleProjection A D S z n) =
      lengthLayerProjection A D S x z n ≫
        (selectedPathModuleEvaluationIso A D S (fun w => w.length = n + 1) z (op x)).inv :=
  moduleMorphismMk_eval A D _ _ x

lemma lengthModuleTransition_layerProjection (S : Set D) (z : D) (n : ℕ) :
    lengthModuleTransition A D S z (Nat.le_succ n) ≫ lengthLayerModuleProjection A D S z n = 0 := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, lengthModuleTransition_eval,
    lengthLayerModuleProjection_eval, CategoryTheory.Functor.map_zero,
    ← Category.assoc, lengthMap_layerProjection, zero_comp]

/-- 固定長加群は、相隣る長さ部分加群の包含の真の cokernel。 -/
def lengthLayerModule_isColimit (S : Set D) (z : D) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (lengthLayerModuleProjection A D S z n)
      (lengthModuleTransition_layerProjection A D S z n)) := by
  apply moduleIsColimitOfEvaluations A D
  intro x
  refine (isColimitMapCoconeCoforkEquiv' (moduleEvaluation A D x)
    (lengthModuleTransition_layerProjection A D S z n)).symm ?_
  refine Cofork.isColimitOfIsos _ (lengthLayer_isColimit A D S x z n) _
    (Iso.refl _) (Iso.refl _) (selectedPathModuleEvaluationIso A D S
      (fun w => w.length = n + 1) z (op x)).symm ?_ ?_ ?_
  · change 𝟙 _ ≫ (moduleEvaluation A D x).map
        (lengthModuleTransition A D S z (Nat.le_succ n)) =
      lengthMap A D S x z (Nat.le_succ n) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, lengthModuleTransition_eval]
  · simp
  · change 𝟙 _ ≫ lengthLayerProjection A D S x z n ≫
        (selectedPathModuleEvaluationIso A D S (fun w => w.length = n + 1) z (op x)).inv =
      (moduleEvaluation A D x).map (lengthLayerModuleProjection A D S z n)
    rw [Category.id_comp, lengthLayerModuleProjection_eval]

instance lengthModuleTransition_hasCokernel (S : Set D) (z : D) (n : ℕ) :
    HasCokernel (lengthModuleTransition A D S z (Nat.le_succ n)) :=
  HasColimit.mk ⟨_, lengthLayerModule_isColimit A D S z n⟩

/-- 長さの随伴次数部分と固定長 path 加群との同型。 -/
def lengthModuleGradedIso (S : Set D) (z : D) (n : ℕ) :
    cokernel (lengthModuleTransition A D S z (Nat.le_succ n)) ≅
      selectedPathModule A D S (fun w => w.length = n + 1) z :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (lengthLayerModule_isColimit A D S z n)

@[reassoc] lemma lengthModuleGradedIso_π (S : Set D) (z : D) (n : ℕ) :
    cokernel.π (lengthModuleTransition A D S z (Nat.le_succ n)) ≫
        (lengthModuleGradedIso A D S z n).hom = lengthLayerModuleProjection A D S z n :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

/-- 加群圏での随伴次数部分の、S 上の自由加群による表示。 -/
def lengthModuleGradedFreeIso (S : Set D) (z : D) (n : ℕ) :
    cokernel (lengthModuleTransition A D S z (Nat.le_succ n)) ≅
      ∐ (fun p : S × LengthWord S n =>
        (freeAt p.1.val).obj (pathSuffixWeight A D p.2.val p.1 z)) :=
  lengthModuleGradedIso A D S z n ≪≫ fixedLengthModuleFreeIso A D S z n

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonLayerModule

/-! ## DerivedComparisonLayerTriangle（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonLayerTriangle.lean） -/

/-! # 長さ filtration の層と加群 cone の導来比較 -/

@[expose] public section DerivedComparisonLayerTriangle

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex CochainComplex Opposite Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def lengthLayerModuleEvaluationShortComplex (S : Set D) (z : D) (n : ℕ) (x : D) :
    ShortComplex (Complex A) :=
  ShortComplex.mk ((moduleEvaluation A D x).map
    (lengthModuleTransition A D S z (Nat.le_succ n)))
    ((moduleEvaluation A D x).map (lengthLayerModuleProjection A D S z n))
    (moduleCompZero_eval A D _ _ (lengthModuleTransition_layerProjection A D S z n) (op x))

lemma lengthLayerModuleEvaluationShortExact (S : Set D) (z : D) (n : ℕ) (x : D) :
    (lengthLayerModuleEvaluationShortComplex A D S z n x).ShortExact := by
  have hc := (isColimitMapCoconeCoforkEquiv' (moduleEvaluation A D x)
    (lengthModuleTransition_layerProjection A D S z n))
      (isColimitOfPreserves (moduleEvaluation A D x) (lengthLayerModule_isColimit A D S z n))
  have hm : Mono ((moduleEvaluation A D x).map
      (lengthModuleTransition A D S z (Nat.le_succ n))) := by
    rw [lengthModuleTransition_eval]
    exact mono_of_mono_fac (lengthMap_inclusion A D S x z (Nat.le_succ n))
  exact
    { exact := (lengthLayerModuleEvaluationShortComplex A D S z n x).exact_of_g_is_cokernel hc
      mono_f := hm
      epi_g := epi_of_isColimit_cofork hc }

/-- 相隣る長さ部分加群の cone から固定長加群への実際の加群射。 -/
def lengthLayerConeDesc (S : Set D) (z : D) (n : ℕ) :
    moduleCone A D (lengthModuleTransition A D S z (Nat.le_succ n)) ⟶
      selectedPathModule A D S (fun w => w.length = n + 1) z :=
  moduleConeDesc A D _ _ (lengthModuleTransition_layerProjection A D S z n)

@[reassoc] lemma lengthLayerConeDesc_inr (S : Set D) (z : D) (n : ℕ) :
    moduleConeInr A D (lengthModuleTransition A D S z (Nat.le_succ n)) ≫
      lengthLayerConeDesc A D S z n = lengthLayerModuleProjection A D S z n :=
  moduleConeDesc_inr A D _ _ _

/-- objectwise 短完全性から cone と固定長加群は擬同型。K-flat 仮定は不要。 -/
lemma lengthLayerConeDesc_quasiIso (S : Set D) (z : D) (n : ℕ) :
    moduleQuasiIso A D (lengthLayerConeDesc A D S z n) := by
  intro x
  rw [lengthLayerConeDesc, moduleConeDesc_eval]
  change QuasiIso (mappingCone.descShortComplex
    (lengthLayerModuleEvaluationShortComplex A D S z n x))
  exact mappingCone.quasiIso_descShortComplex (lengthLayerModuleEvaluationShortExact A D S z n x)

/-- 導来圏では実際の加群 cone と固定長加群が同型になる。 -/
def lengthLayerDerivedConeIso (S : Set D) (z : D) (n : ℕ) :
    (moduleToDerived A D).obj
        (moduleCone A D (lengthModuleTransition A D S z (Nat.le_succ n))) ≅
      (moduleToDerived A D).obj (selectedPathModule A D S (fun w => w.length = n + 1) z) :=
  moduleDerivedIso A D _ (lengthLayerConeDesc_quasiIso A D S z n)

/-- 相隣る長さ部分加群と固定長 path 加群からなる導来三角形。 -/
def lengthLayerDerivedTriangle (S : Set D) (z : D) (n : ℕ) :
    Triangle (DerivedModuleCategory A D) :=
  Triangle.mk ((moduleToDerived A D).map (lengthModuleTransition A D S z (Nat.le_succ n)))
    ((moduleToDerived A D).map (lengthLayerModuleProjection A D S z n))
    ((lengthLayerDerivedConeIso A D S z n).inv ≫
      (moduleDerivedConeTriangle A D (lengthModuleTransition A D S z (Nat.le_succ n))).mor₃)

def lengthLayerDerivedTriangleIso (S : Set D) (z : D) (n : ℕ) :
    moduleDerivedConeTriangle A D (lengthModuleTransition A D S z (Nat.le_succ n)) ≅
      lengthLayerDerivedTriangle A D S z n := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (lengthLayerDerivedConeIso A D S z n) ?_ ?_ ?_
  · change (moduleToDerived A D).map (lengthModuleTransition A D S z (Nat.le_succ n)) ≫
        𝟙 _ = 𝟙 _ ≫ (moduleToDerived A D).map
          (lengthModuleTransition A D S z (Nat.le_succ n))
    rw [Category.comp_id, Category.id_comp]
  · change (moduleToDerived A D).map
        (moduleConeInr A D (lengthModuleTransition A D S z (Nat.le_succ n))) ≫
        (moduleToDerived A D).map (lengthLayerConeDesc A D S z n) =
      𝟙 _ ≫ (moduleToDerived A D).map (lengthLayerModuleProjection A D S z n)
    rw [← CategoryTheory.Functor.map_comp, lengthLayerConeDesc_inr, Category.id_comp]
  · change (moduleDerivedConeTriangle A D
        (lengthModuleTransition A D S z (Nat.le_succ n))).mor₃ ≫ (𝟙 _)⟦(1 : ℤ)⟧' =
      (lengthLayerDerivedConeIso A D S z n).hom ≫
        (lengthLayerDerivedConeIso A D S z n).inv ≫ _
    rw [CategoryTheory.Functor.map_id, Category.comp_id, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]

lemma lengthLayerDerivedTriangle_distinguished (S : Set D) (z : D) (n : ℕ) :
    lengthLayerDerivedTriangle A D S z n ∈ distTriang (DerivedModuleCategory A D) :=
  isomorphic_distinguished _ (moduleDerivedConeTriangle_distinguished A D
    (lengthModuleTransition A D S z (Nat.le_succ n))) _
      (lengthLayerDerivedTriangleIso A D S z n).symm

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonLayerTriangle

/-! ## DerivedComparisonFreeExtension（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonFreeExtension.lean） -/

/-! # K-flat 係数からの自由加群を一対象環からの導来延長で計算する

置換は通常の dg 加群の射影置換だけを使う。dg 圏の分解は使わない。
-/

@[expose] public section DerivedComparisonFreeExtension

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 一対象環 A から指定対象への dg 関手。 -/
def pointDGFunctor (b : D) : DGFunctor A PUnit.{1} D where
  obj _ := b
  map _ _ := eId (Complex A) b
  map_id _ := Category.id_comp _
  map_comp _ _ _ := by
    have h : (eId (Complex A) b ▷ homObject A D b b) ≫ eComp (Complex A) b b b =
        (λ_ (homObject A D b b)).hom := by
      apply (cancel_epi (λ_ (homObject A D b b)).inv).mp
      rw [e_id_comp, Iso.inv_hom_id]
    change (λ_ (𝟙_ (Complex A))).hom ≫ eId (Complex A) b =
      (eId (Complex A) b ⊗ₘ eId (Complex A) b) ≫ eComp (Complex A) b b b
    rw [tensorHom_def', Category.assoc, h, leftUnitor_naturality]

/-- 一対象環からの延長は、複体の同値を通じて自由加群関手になる。 -/
def pointExtensionFreeFunctorIso (b : D) :
    (ringModuleEquivalence A).inverse ⋙
      (dgModuleExtension A PUnit.{1} D (pointDGFunctor A D b)).onClosed ≅ freeAt b := by
  let adj := (ringModuleEquivalence A).symm.toAdjunction.comp
    (dgModuleExtensionRestrictionAdjunction A PUnit.{1} D (pointDGFunctor A D b))
  let e : (moduleRestriction A PUnit.{1} D (pointDGFunctor A D b).op ⋙
      (ringModuleEquivalence A).functor) ≅ moduleEvaluation A D b :=
    eqToIso (moduleRestriction_comp_evaluation A PUnit.{1} D
      (pointDGFunctor A D b).op PUnit.unit)
  exact Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) (freeEvaluationAdjunction A D b)

def pointExtensionRingIso (b : D) (M : ModuleCategory A PUnit.{1}) :
    (dgModuleExtension A PUnit.{1} D (pointDGFunctor A D b)).onClosed.obj M ≅
      (freeAt b).obj ((moduleEvaluation A PUnit.{1} PUnit.unit).obj M) :=
  (dgModuleExtension A PUnit.{1} D (pointDGFunctor A D b)).onClosed.mapIso
      ((ringModuleEquivalence A).unitIso.app M) ≪≫
    (pointExtensionFreeFunctorIso A D b).app ((ringModuleEquivalence A).functor.obj M)

variable (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgExtension_relativeKFlat_quasiIso {M N : ModuleCategory A D}
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hN : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) N))
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A E ((dgModuleExtension A D E F).onClosed.map f) := by
  intro e
  rw [dgModuleExtension_map_eval]
  exact BalancedTensor.rightTensor_relativeKFlat_quasiIso A D
    ((functorGraph A D E F).leftAt e) hM hN f hf

/-- 相対 K-flat 加群の導来延長は underived 延長で計算できる。 -/
def relativeKFlatExtensionComputation (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    (dgDerivedExtension A D E F).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj M) :=
  dgDerivedExtensionResolutionComputation A D E F (moduleCanonicalProjectiveResolution A D M) ≪≫
    moduleDerivedIso A E _ (dgExtension_relativeKFlat_quasiIso A D E F
      (moduleHomotopicallyProjective_relativeKFlat A D
        (moduleCanonicalProjectiveResolution A D M).projective) hM
      (moduleCanonicalProjectiveResolution A D M).π
      (moduleCanonicalProjectiveResolution A D M).quasiIso)

lemma coefficientRingModule_relativeKFlat (K : Complex A) (hK : complexKFlat A K) :
    moduleRelativeKFlat A PUnit.{1} (ringModule A K) := by
  intro N hN
  exact cochainAcyclic_of_iso (hK _ (hN PUnit.unit))
    (BalancedTensor.ringIso A (ringModule A K) N).symm

/-- K-flat 係数の underived 自由加群は、一対象環からの導来延長で得られる。 -/
def derivedFreeAtKFlatIso (b : D) (K : Complex A) (hK : complexKFlat A K) :
    (dgDerivedExtension A PUnit.{1} D (pointDGFunctor A D b)).obj
        ((moduleToDerived A PUnit.{1}).obj (ForgetEnrichment.of (Complex A) (ringModule A K))) ≅
      (moduleToDerived A D).obj ((freeAt b).obj K) :=
  relativeKFlatExtensionComputation A PUnit.{1} D (pointDGFunctor A D b)
      (ForgetEnrichment.of (Complex A) (ringModule A K))
      (coefficientRingModule_relativeKFlat A K hK) ≪≫
    (moduleToDerived A D).mapIso
      (pointExtensionRingIso A D b (ForgetEnrichment.of (Complex A) (ringModule A K)))

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonFreeExtension
