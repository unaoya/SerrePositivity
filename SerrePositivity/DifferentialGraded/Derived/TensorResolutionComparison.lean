module
public import SerrePositivity.DifferentialGraded.Derived.TensorBifunctorChoice
public import SerrePositivity.DifferentialGraded.Derived.RightTensorResolution

/-! # 任意解像度のtensor計算と左自然性・推移整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable {M : ModuleCategory A D}

/-- 指定解像度で計算するtensorは左加群変数の関手。 -/
def moduleProjectiveResolutionTensorLeftFunctor (P : ModuleProjectiveResolution A D M) :
    LeftModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A) :=
  BalancedTensor.leftTensorFunctor A D (ForgetEnrichment.to (Complex A) P.obj) ⋙ DerivedCategory.Q

/-- 二つの任意解像度による計算の比較は左加群変数にも自然。 -/
def moduleProjectiveResolutionTensorLeftIso (P Q : ModuleProjectiveResolution A D M) :
    moduleProjectiveResolutionTensorLeftFunctor A D P ≅
      moduleProjectiveResolutionTensorLeftFunctor A D Q :=
  NatIso.ofComponents
    (fun L => moduleProjectiveResolutionTensorIso A D P Q (ForgetEnrichment.to (Complex A) L))
    (by
      intro L L' g
      change DerivedCategory.Q.map (BalancedTensor.map A D (𝟙 P.obj) g) ≫
          DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D
            (ForgetEnrichment.to (Complex A) L')).map (P.comparison Q)) =
        DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D
          (ForgetEnrichment.to (Complex A) L)).map (P.comparison Q)) ≫
            DerivedCategory.Q.map (BalancedTensor.map A D (𝟙 Q.obj) g)
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      exact congrArg
        (fun f : (BalancedTensor.rightTensorFunctor A D
          (ForgetEnrichment.to (Complex A) L)).obj P.obj ⟶
            (BalancedTensor.rightTensorFunctor A D
              (ForgetEnrichment.to (Complex A) L')).obj Q.obj => DerivedCategory.Q.map f)
        ((BalancedTensor.rightTensorLeftMap A D g).naturality (P.comparison Q)).symm)

lemma moduleProjectiveResolutionTensorLeftIso_self (P : ModuleProjectiveResolution A D M) :
    moduleProjectiveResolutionTensorLeftIso A D P P = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext L
  change (moduleProjectiveResolutionTensorIso A D P P
    (ForgetEnrichment.to (Complex A) L)).hom = 𝟙 _
  exact congrArg Iso.hom
    (moduleProjectiveResolutionTensorIso_self A D P (ForgetEnrichment.to (Complex A) L))

lemma moduleProjectiveResolutionTensorLeftIso_trans (P Q R : ModuleProjectiveResolution A D M) :
    moduleProjectiveResolutionTensorLeftIso A D P Q ≪≫
        moduleProjectiveResolutionTensorLeftIso A D Q R =
      moduleProjectiveResolutionTensorLeftIso A D P R := by
  apply Iso.ext
  apply NatTrans.ext
  funext L
  exact congrArg Iso.hom
    (moduleProjectiveResolutionTensorIso_trans A D P Q R (ForgetEnrichment.to (Complex A) L))

/-- 両変数導来tensorは、選ばれた族とは別の任意の右射影解像度でも計算できる。 -/
def moduleTensorBifunctorResolutionComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) (P : ModuleProjectiveResolution A D M) :
    ((moduleResolutionDerivedTensorBifunctor A D R).obj
      ((leftModuleToDerived A D).obj L)).obj ((moduleToDerived A D).obj M) ≅
      DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D
        (ForgetEnrichment.to (Complex A) L)).obj P.obj) :=
  moduleResolutionDerivedTensorBifunctorComputation A D R L M ≪≫
    moduleProjectiveResolutionTensorIso A D (R M) P (ForgetEnrichment.to (Complex A) L)

/-- 計算に使う解像度の変更は既存の比較射と整合する。 -/
lemma moduleTensorBifunctorResolutionComputation_trans
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) (P Q : ModuleProjectiveResolution A D M) :
    moduleTensorBifunctorResolutionComputation A D R L P ≪≫
        moduleProjectiveResolutionTensorIso A D P Q (ForgetEnrichment.to (Complex A) L) =
      moduleTensorBifunctorResolutionComputation A D R L Q := by
  unfold moduleTensorBifunctorResolutionComputation
  rw [Iso.trans_assoc, moduleProjectiveResolutionTensorIso_trans]

end SerrePositivity.DifferentialGraded
