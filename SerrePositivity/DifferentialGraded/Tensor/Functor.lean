module
public import SerrePositivity.DifferentialGraded.Tensor.Maps
public import SerrePositivity.DifferentialGraded.Module.LeftMorphisms

/-! # 右dg加群・左dg加群上のbalanced tensor双関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma rightAction_morphism {M M' : ModuleCategory A D} (f : M ⟶ M') (x y : D) :
    rightAction A D (ForgetEnrichment.to (Complex A) M) x y ≫ (moduleEvaluation A D x).map f =
      ((moduleEvaluation A D y).map f ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫
        rightAction A D (ForgetEnrichment.to (Complex A) M') x y := by
  unfold rightAction
  rw [Category.assoc, moduleMorphism_action_chain]
  let fy : (ForgetEnrichment.to (Complex A) M).obj (op y) ⟶
      (ForgetEnrichment.to (Complex A) M').obj (op y) := (moduleEvaluation A D y).map f
  have h := signedSwap_naturality fy (𝟙 (x ⟶[Complex A] y))
  change (signedSwap ((ForgetEnrichment.to (Complex A) M).obj (op y))
      (x ⟶[Complex A] y)).hom ≫ (𝟙 (x ⟶[Complex A] y) ⊗ₘ fy) ≫
        moduleActionChain A (ForgetEnrichment.to (Complex A) M') (op y) (op x) =
    (fy ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫
      (signedSwap ((ForgetEnrichment.to (Complex A) M').obj (op y))
        (x ⟶[Complex A] y)).hom ≫
          moduleActionChain A (ForgetEnrichment.to (Complex A) M') (op y) (op x)
  simpa only [Category.assoc] using congrArg (fun t => t ≫
    moduleActionChain A (ForgetEnrichment.to (Complex A) M') (op y) (op x)) h.symm

lemma leftAction_morphism {N N' : LeftModuleCategory A D} (g : N ⟶ N') (x y : D) :
    leftAction A D (ForgetEnrichment.to (Complex A) N) x y ≫ (leftModuleEvaluation A D y).map g =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ (leftModuleEvaluation A D x).map g) ≫
        leftAction A D (ForgetEnrichment.to (Complex A) N') x y :=
  leftModuleMorphism_action_chain A D g x y

/-- 閉零加群圏の両方の射に関するbalanced tensorのmap。 -/
def map {M M' : ModuleCategory A D} {N N' : LeftModuleCategory A D} (f : M ⟶ M') (g : N ⟶ N') :
    obj A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) ⟶
      obj A D (ForgetEnrichment.to (Complex A) M') (ForgetEnrichment.to (Complex A) N') :=
  mapOfFamilies A D (fun x => (moduleEvaluation A D x).map f)
    (fun x => (leftModuleEvaluation A D x).map g)
    (rightAction_morphism A D f) (leftAction_morphism A D g)

@[reassoc (attr := simp)]
lemma ι_map {M M' : ModuleCategory A D} {N N' : LeftModuleCategory A D}
    (f : M ⟶ M') (g : N ⟶ N') (x : D) :
    ι A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x ≫ map A D f g =
      ((moduleEvaluation A D x).map f ⊗ₘ (leftModuleEvaluation A D x).map g) ≫
        ι A D (ForgetEnrichment.to (Complex A) M') (ForgetEnrichment.to (Complex A) N') x :=
  ι_mapOfFamilies A D _ _ _ _ x

lemma map_id (M : ModuleCategory A D) (N : LeftModuleCategory A D) :
    map A D (𝟙 M) (𝟙 N) = 𝟙 _ := by
  apply hom_ext
  intro x
  simp

lemma map_comp {M M' M'' : ModuleCategory A D} {N N' N'' : LeftModuleCategory A D}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    map A D (f ≫ f') (g ≫ g') = map A D f g ≫ map A D f' g' := by
  apply hom_ext
  intro x
  simp only [ι_map, ι_map_assoc, CategoryTheory.Functor.map_comp, tensorHom_comp_tensorHom_assoc]

/-- 両変数で共変な、実際の閉零加群圏の積からの関手。 -/
def functor : ModuleCategory A D × LeftModuleCategory A D ⥤ Complex A where
  obj MN := obj A D (ForgetEnrichment.to (Complex A) MN.1) (ForgetEnrichment.to (Complex A) MN.2)
  map fg := map A D fg.1 fg.2
  map_id MN := map_id A D MN.1 MN.2
  map_comp fg gh := map_comp A D fg.1 gh.1 fg.2 gh.2

end SerrePositivity.DifferentialGraded.BalancedTensor
