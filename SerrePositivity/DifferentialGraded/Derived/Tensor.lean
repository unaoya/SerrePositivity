module

public import SerrePositivity.DifferentialGraded.Derived.Projective
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-!
# Derived.Tensor

## 概要
10 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## RightTensor（旧 SerrePositivity/DifferentialGraded/Derived/RightTensor.lean） -/

/-! # 固定左dg加群との導来tensor

指定quasiIso局所化から射影解像度をK(D)へ取り、既存tensor関手をK(A)、D(A)へ合成する。
-/

@[expose] public section RightTensor
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma moduleTensorDerived_map_eq_of_homotopy_map_eq (L : LeftModule A D)
    {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g) :
    DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map f) =
      DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map g) := by
  obtain ⟨ht⟩ := (moduleToHomotopy_map_eq_iff A D f g).1 h
  exact DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} A)
    (BalancedTensor.rightTensorMap_homotopy A D L ht).some

/-- 解像度族を指定した固定左加群との導来tensor。 -/
def moduleResolutionDerivedTensor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (L : LeftModule A D) :
    DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A) :=
  moduleDerivedResolutionFunctor A D R ⋙
    BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh

def moduleTensorHomotopyComputation (L : LeftModule A D) (M : ModuleCategory A D) :
    (BalancedTensor.rightTensorHomotopyFunctor A D L).obj ((moduleToHomotopy A D).obj M) ≅
      (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj
        ((BalancedTensor.rightTensorFunctor A D L).obj M) :=
  eqToIso (congrArg (fun F => F.obj M) (BalancedTensor.rightTensorHomotopyFunctor_fac A D L))

/-- 主導来圏の対象での、実際の射影解像度による計算。 -/
def moduleResolutionDerivedTensorComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModule A D) (M : ModuleCategory A D) :
    (moduleResolutionDerivedTensor A D R L).obj ((moduleToDerived A D).obj M) ≅
      DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D L).obj (R M).obj) :=
  (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).mapIso
      (moduleDerivedResolutionComputation A D R M) ≪≫
    DerivedCategory.Qh.mapIso (moduleTensorHomotopyComputation A D L (R M).obj) ≪≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app
        ((BalancedTensor.rightTensorFunctor A D L).obj (R M).obj)

/-- 既存の標準semifree解像度から作る固定左加群との導来tensor。 -/
def moduleDerivedTensorRight (L : LeftModule A D) :
    DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A) :=
  moduleResolutionDerivedTensor A D (moduleCanonicalProjectiveResolution A D) L

/-- 任意の二つの解像度族から作った導来tensorは自然同型。 -/
def moduleResolutionDerivedTensorIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (L : LeftModule A D) :
    moduleResolutionDerivedTensor A D R L ≅ moduleResolutionDerivedTensor A D S L :=
  Functor.isoWhiskerRight (moduleDerivedResolutionIso A D R S)
    (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh)

lemma moduleResolutionDerivedTensorIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (L : LeftModule A D) :
    moduleResolutionDerivedTensorIso A D R R L = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).map
    ((moduleDerivedResolutionIso A D R R).hom.app X) = 𝟙 _
  rw [moduleDerivedResolutionIso_self]
  exact (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).map_id _

lemma moduleResolutionDerivedTensorIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (L : LeftModule A D) :
    moduleResolutionDerivedTensorIso A D R S L ≪≫ moduleResolutionDerivedTensorIso A D S T L =
      moduleResolutionDerivedTensorIso A D R T L := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).map
      ((moduleDerivedResolutionIso A D R S).hom.app X) ≫
    (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).map
      ((moduleDerivedResolutionIso A D S T).hom.app X) = _
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun f =>
    (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).map f)
    (NatTrans.congr_app (congrArg Iso.hom (moduleDerivedResolutionIso_trans A D R S T)) X)

end SerrePositivity.DifferentialGraded
end

end RightTensor

/-! ## RightTensorResolution（旧 SerrePositivity/DifferentialGraded/Derived/RightTensorResolution.lean） -/

/-! # 任意の証明付き射影解像度による導来tensor計算 -/

@[expose] public section RightTensorResolution
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable {M : ModuleCategory A D}

def moduleProjectiveResolutionTensorIso (P Q : ModuleProjectiveResolution A D M)
    (L : LeftModule A D) :
    DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D L).obj P.obj) ≅
      DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D L).obj Q.obj) := by
  have := BalancedTensor.rightTensor_projective_quasiIso A D L P.projective Q.projective
    (P.comparison Q) (P.comparison_quasiIso Q)
  exact asIso (DerivedCategory.Q.map
    ((BalancedTensor.rightTensorFunctor A D L).map (P.comparison Q)))

lemma moduleProjectiveResolutionTensorIso_hom (P Q : ModuleProjectiveResolution A D M)
    (L : LeftModule A D) :
    (moduleProjectiveResolutionTensorIso A D P Q L).hom =
      DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map (P.comparison Q)) := rfl

lemma moduleProjectiveResolutionTensorIso_self (P : ModuleProjectiveResolution A D M)
    (L : LeftModule A D) : moduleProjectiveResolutionTensorIso A D P P L = Iso.refl _ := by
  apply Iso.ext
  change DerivedCategory.Q.map
    ((BalancedTensor.rightTensorFunctor A D L).map (P.comparison P)) = 𝟙 _
  have h := moduleTensorDerived_map_eq_of_homotopy_map_eq A D L
    (P.comparison_self.trans ((moduleToHomotopy A D).map_id P.obj).symm)
  simpa only [CategoryTheory.Functor.map_id] using h

lemma moduleProjectiveResolutionTensorIso_trans (P Q R : ModuleProjectiveResolution A D M)
    (L : LeftModule A D) :
    moduleProjectiveResolutionTensorIso A D P Q L ≪≫ moduleProjectiveResolutionTensorIso A D Q R L =
      moduleProjectiveResolutionTensorIso A D P R L := by
  apply Iso.ext
  change DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map (P.comparison Q)) ≫
      DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map (Q.comparison R)) =
    DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map (P.comparison R))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact moduleTensorDerived_map_eq_of_homotopy_map_eq A D L
    (((moduleToHomotopy A D).map_comp (P.comparison Q) (Q.comparison R)).trans
      (P.comparison_comp Q R))

/-- 導来tensorの値は任意の射影的解像度で計算できる。 -/
def moduleDerivedTensorRightResolutionComputation (P : ModuleProjectiveResolution A D M)
    (L : LeftModule A D) :
    (moduleDerivedTensorRight A D L).obj ((moduleToDerived A D).obj M) ≅
      DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D L).obj P.obj) :=
  moduleResolutionDerivedTensorComputation A D (moduleCanonicalProjectiveResolution A D) L M ≪≫
    moduleProjectiveResolutionTensorIso A D (moduleCanonicalProjectiveResolution A D M) P L

end SerrePositivity.DifferentialGraded
end

end RightTensorResolution

/-! ## RightTensorLeftFunctor（旧 SerrePositivity/DifferentialGraded/Derived/RightTensorLeftFunctor.lean） -/

/-! # 左加群の閉零圏に関する導来tensorの関手性 -/

@[expose] public section RightTensorLeftFunctor
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 左加群の射を、右変数を導来化したtensor関手間の自然変換へ送る。 -/
def moduleResolutionDerivedTensorLeftFunctor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    LeftModuleCategory A D ⥤ (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  BalancedTensor.rightTensorHomotopyBifunctor A D ⋙
    (Functor.whiskeringLeft (DerivedModuleCategory A D) (ModuleHomotopyCategory A D)
      (_root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ))).obj
        (moduleDerivedResolutionFunctor A D R) ⋙
    (Functor.whiskeringRight (DerivedModuleCategory A D)
      (_root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ)) (DerivedCategory (ModuleCat.{u} A))).obj
        DerivedCategory.Qh

lemma moduleResolutionDerivedTensorLeftFunctor_obj
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (L : LeftModuleCategory A D) :
    (moduleResolutionDerivedTensorLeftFunctor A D R).obj L =
      moduleResolutionDerivedTensor A D R (ForgetEnrichment.to (Complex A) L) := rfl

lemma moduleResolutionDerivedTensorLeftFunctor_map_app
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {L L' : LeftModuleCategory A D} (g : L ⟶ L') (X : DerivedModuleCategory A D) :
    ((moduleResolutionDerivedTensorLeftFunctor A D R).map g).app X =
      DerivedCategory.Qh.map ((BalancedTensor.rightTensorHomotopyLeftMap A D g).app
        ((moduleDerivedResolutionFunctor A D R).obj X)) := rfl

/-- 標準解像度を用いた導来tensorは左加群の通常射に関して関手的。 -/
def moduleDerivedTensorLeftFunctor :
    LeftModuleCategory A D ⥤ (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  moduleResolutionDerivedTensorLeftFunctor A D (moduleCanonicalProjectiveResolution A D)

lemma moduleDerivedTensorLeftFunctor_obj (L : LeftModuleCategory A D) :
    (moduleDerivedTensorLeftFunctor A D).obj L =
      moduleDerivedTensorRight A D (ForgetEnrichment.to (Complex A) L) := rfl

end SerrePositivity.DifferentialGraded
end

end RightTensorLeftFunctor

/-! ## TensorChoiceLeft（旧 SerrePositivity/DifferentialGraded/Derived/TensorChoiceLeft.lean） -/

/-! # 解像度族比較の左加群変数に関する自然性 -/

@[expose] public section TensorChoiceLeft
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 固定左加群での比較は左加群のすべての射に関して自然。 -/
def moduleResolutionDerivedTensorLeftIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedTensorLeftFunctor A D R ≅
      moduleResolutionDerivedTensorLeftFunctor A D S :=
  NatIso.ofComponents
    (fun L => moduleResolutionDerivedTensorIso A D R S (ForgetEnrichment.to (Complex A) L))
    (by
      intro L L' g
      apply NatTrans.ext
      funext X
      let τ : BalancedTensor.rightTensorHomotopyFunctor A D (ForgetEnrichment.to (Complex A) L) ⋙
          DerivedCategory.Qh ⟶
        BalancedTensor.rightTensorHomotopyFunctor A D (ForgetEnrichment.to (Complex A) L') ⋙
          DerivedCategory.Qh :=
        Functor.whiskerRight (BalancedTensor.rightTensorHomotopyLeftMap A D g) DerivedCategory.Qh
      change τ.app ((moduleDerivedResolutionFunctor A D R).obj X) ≫
          (BalancedTensor.rightTensorHomotopyFunctor A D
            (ForgetEnrichment.to (Complex A) L') ⋙ DerivedCategory.Qh).map
              ((moduleDerivedResolutionIso A D R S).hom.app X) =
        (BalancedTensor.rightTensorHomotopyFunctor A D
          (ForgetEnrichment.to (Complex A) L) ⋙ DerivedCategory.Qh).map
            ((moduleDerivedResolutionIso A D R S).hom.app X) ≫
              τ.app ((moduleDerivedResolutionFunctor A D S).obj X)
      exact (τ.naturality ((moduleDerivedResolutionIso A D R S).hom.app X)).symm)

lemma moduleResolutionDerivedTensorLeftIso_hom_app
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) :
    (moduleResolutionDerivedTensorLeftIso A D R S).hom.app L =
      (moduleResolutionDerivedTensorIso A D R S (ForgetEnrichment.to (Complex A) L)).hom := rfl

lemma moduleResolutionDerivedTensorLeftIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedTensorLeftIso A D R R = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext L
  change (moduleResolutionDerivedTensorIso A D R R
    (ForgetEnrichment.to (Complex A) L)).hom =
      𝟙 (moduleResolutionDerivedTensor A D R (ForgetEnrichment.to (Complex A) L))
  exact congrArg Iso.hom
    (moduleResolutionDerivedTensorIso_self A D R (ForgetEnrichment.to (Complex A) L))

lemma moduleResolutionDerivedTensorLeftIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedTensorLeftIso A D R S ≪≫ moduleResolutionDerivedTensorLeftIso A D S T =
      moduleResolutionDerivedTensorLeftIso A D R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext L
  simpa only [Iso.trans_hom, NatTrans.comp_app, moduleResolutionDerivedTensorLeftIso_hom_app]
    using congrArg Iso.hom
      (moduleResolutionDerivedTensorIso_trans A D R S T (ForgetEnrichment.to (Complex A) L))

end SerrePositivity.DifferentialGraded
end

end TensorChoiceLeft

/-! ## LeftTensorInversion（旧 SerrePositivity/DifferentialGraded/Derived/LeftTensorInversion.lean） -/

/-! # 左準同型による導来tensor自然変換の可逆性 -/

@[expose] public section LeftTensorInversion
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma moduleProjectiveTensorLeftMap_isIso {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) {L L' : LeftModuleCategory A D} (g : L ⟶ L')
    (hg : leftModuleQuasiIso A D g) :
    IsIso (DerivedCategory.Qh.map ((BalancedTensor.rightTensorHomotopyLeftMap A D g).app
      ((moduleToHomotopy A D).obj M))) := by
  rw [BalancedTensor.rightTensorHomotopyLeftMap_app]
  let f := BalancedTensor.map A D (𝟙 M) g
  have hf : QuasiIso f := moduleHomotopicallyProjective_preserves_leftQuasiIso A D hM g hg
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) f).2 hf
  have he := NatIso.naturality_2 (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)) f
  change IsIso (( _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ) ⋙
    DerivedCategory.Qh).map f)
  rw [← he]
  infer_instance

lemma moduleResolutionDerivedTensorLeftFunctor_inverts
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    (leftModuleQuasiIso A D).IsInvertedBy (moduleResolutionDerivedTensorLeftFunctor A D R) := by
  intro L L' g hg
  let τ : BalancedTensor.rightTensorHomotopyFunctor A D (ForgetEnrichment.to (Complex A) L) ⋙
      DerivedCategory.Qh ⟶
    BalancedTensor.rightTensorHomotopyFunctor A D (ForgetEnrichment.to (Complex A) L') ⋙
      DerivedCategory.Qh := Functor.whiskerRight (BalancedTensor.rightTensorHomotopyLeftMap A D g)
    DerivedCategory.Qh
  change IsIso (Functor.whiskerLeft (moduleDerivedResolutionFunctor A D R) τ)
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (moduleToDerived A D) X
  let eR : (moduleDerivedResolutionFunctor A D R).obj X ≅
      (moduleToHomotopy A D).obj (R M).obj :=
    (moduleDerivedResolutionFunctor A D R).mapIso e.symm ≪≫
      moduleDerivedResolutionComputation A D R M
  change IsIso (τ.app ((moduleDerivedResolutionFunctor A D R).obj X))
  rw [NatTrans.isIso_app_iff_of_iso τ eR]
  exact moduleProjectiveTensorLeftMap_isIso A D (R M).projective g hg

lemma moduleDerivedTensorLeftFunctor_inverts :
    (leftModuleQuasiIso A D).IsInvertedBy (moduleDerivedTensorLeftFunctor A D) :=
  moduleResolutionDerivedTensorLeftFunctor_inverts A D (moduleCanonicalProjectiveResolution A D)

end SerrePositivity.DifferentialGraded
end

end LeftTensorInversion

/-! ## TensorBifunctor（旧 SerrePositivity/DifferentialGraded/Derived/TensorBifunctor.lean） -/

/-! # 両変数を指定局所化した導来balanced tensor -/

@[expose] public section TensorBifunctor
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 射影解像度族を指定した、左右の導来加群圏上のtensor双関手。 -/
def moduleResolutionDerivedTensorBifunctor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    DerivedLeftModuleCategory A D ⥤
      (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  Localization.Construction.lift (moduleResolutionDerivedTensorLeftFunctor A D R)
    (moduleResolutionDerivedTensorLeftFunctor_inverts A D R)

lemma moduleResolutionDerivedTensorBifunctor_fac
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    leftModuleToDerived A D ⋙ moduleResolutionDerivedTensorBifunctor A D R =
      moduleResolutionDerivedTensorLeftFunctor A D R :=
  Localization.Construction.fac _ _

/-- 標準semifree解像度による両変数導来tensor。 -/
def moduleDerivedTensorBifunctor : DerivedLeftModuleCategory A D ⥤
    (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  moduleResolutionDerivedTensorBifunctor A D (moduleCanonicalProjectiveResolution A D)

lemma moduleDerivedTensorBifunctor_fac :
    leftModuleToDerived A D ⋙ moduleDerivedTensorBifunctor A D =
      moduleDerivedTensorLeftFunctor A D :=
  moduleResolutionDerivedTensorBifunctor_fac A D (moduleCanonicalProjectiveResolution A D)

/-- 左変数の局所化前で、既存の右変数導来tensorと厳密に一致する。 -/
lemma moduleResolutionDerivedTensorBifunctor_obj
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) :
    (moduleResolutionDerivedTensorBifunctor A D R).obj ((leftModuleToDerived A D).obj L) =
      moduleResolutionDerivedTensor A D R (ForgetEnrichment.to (Complex A) L) :=
  congrArg (fun F => F.obj L) (moduleResolutionDerivedTensorBifunctor_fac A D R)

/-- 任意の右射影解像度族を用いた、両局所化からの具体的tensor計算。 -/
def moduleResolutionDerivedTensorBifunctorComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) (M : ModuleCategory A D) :
    ((moduleResolutionDerivedTensorBifunctor A D R).obj
      ((leftModuleToDerived A D).obj L)).obj ((moduleToDerived A D).obj M) ≅
    DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D
      (ForgetEnrichment.to (Complex A) L)).obj (R M).obj) :=
  (eqToIso (moduleResolutionDerivedTensorBifunctor_obj A D R L)).app
    ((moduleToDerived A D).obj M) ≪≫
      moduleResolutionDerivedTensorComputation A D R (ForgetEnrichment.to (Complex A) L) M

end SerrePositivity.DifferentialGraded
end

end TensorBifunctor

/-! ## TensorBifunctorChoice（旧 SerrePositivity/DifferentialGraded/Derived/TensorBifunctorChoice.lean） -/

/-! # 両変数導来tensorの解像度族選択独立性 -/

@[expose] public section TensorBifunctorChoice
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

def moduleResolutionDerivedTensorBifunctorFacIso
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    leftModuleToDerived A D ⋙ moduleResolutionDerivedTensorBifunctor A D R ≅
      moduleResolutionDerivedTensorLeftFunctor A D R :=
  eqToIso (moduleResolutionDerivedTensorBifunctor_fac A D R)

instance moduleResolutionDerivedTensorBifunctor_lifting
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    Localization.Lifting (leftModuleToDerived A D) (leftModuleQuasiIso A D)
      (moduleResolutionDerivedTensorLeftFunctor A D R)
      (moduleResolutionDerivedTensorBifunctor A D R) :=
  ⟨moduleResolutionDerivedTensorBifunctorFacIso A D R⟩

/-- 両変数を局所化したtensor双関手の、解像度族変更に対する自然同型。 -/
def moduleResolutionDerivedTensorBifunctorIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedTensorBifunctor A D R ≅ moduleResolutionDerivedTensorBifunctor A D S :=
  Localization.liftNatIso (leftModuleToDerived A D) (leftModuleQuasiIso A D)
    (moduleResolutionDerivedTensorLeftFunctor A D R) (moduleResolutionDerivedTensorLeftFunctor A
      D S)
    (moduleResolutionDerivedTensorBifunctor A D R) (moduleResolutionDerivedTensorBifunctor A D S)
    (moduleResolutionDerivedTensorLeftIso A D R S)

lemma moduleResolutionDerivedTensorBifunctorIso_hom_app
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : LeftModuleCategory A
      D) :
    (moduleResolutionDerivedTensorBifunctorIso A D R S).hom.app ((leftModuleToDerived A D).obj M) =
      (moduleResolutionDerivedTensorBifunctorFacIso A D R).hom.app M ≫
        (moduleResolutionDerivedTensorLeftIso A D R S).hom.app M ≫
          (moduleResolutionDerivedTensorBifunctorFacIso A D S).inv.app M :=
  Localization.liftNatTrans_app (leftModuleToDerived A D) (leftModuleQuasiIso A D)
    (moduleResolutionDerivedTensorLeftFunctor A D R) (moduleResolutionDerivedTensorLeftFunctor A
      D S)
    (moduleResolutionDerivedTensorBifunctor A D R) (moduleResolutionDerivedTensorBifunctor A D S)
    (moduleResolutionDerivedTensorLeftIso A D R S).hom M

lemma moduleResolutionDerivedTensorBifunctorIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedTensorBifunctorIso A D R R = Iso.refl _ := by
  apply Iso.ext
  change Localization.liftNatTrans (leftModuleToDerived A D) (leftModuleQuasiIso A D)
    (moduleResolutionDerivedTensorLeftFunctor A D R) (moduleResolutionDerivedTensorLeftFunctor A
      D R)
    (moduleResolutionDerivedTensorBifunctor A D R) (moduleResolutionDerivedTensorBifunctor A D R)
    (moduleResolutionDerivedTensorLeftIso A D R R).hom = 𝟙 _
  rw [moduleResolutionDerivedTensorLeftIso_self, Iso.refl_hom, Localization.liftNatTrans_id]

lemma moduleResolutionDerivedTensorBifunctorIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedTensorBifunctorIso A D R S ≪≫
      moduleResolutionDerivedTensorBifunctorIso A D S T =
      moduleResolutionDerivedTensorBifunctorIso A D R T := by
  apply Iso.ext
  change Localization.liftNatTrans (leftModuleToDerived A D) (leftModuleQuasiIso A D)
    (moduleResolutionDerivedTensorLeftFunctor A D R) (moduleResolutionDerivedTensorLeftFunctor A
      D S)
    (moduleResolutionDerivedTensorBifunctor A D R) (moduleResolutionDerivedTensorBifunctor A D S)
    (moduleResolutionDerivedTensorLeftIso A D R S).hom ≫
    Localization.liftNatTrans (leftModuleToDerived A D) (leftModuleQuasiIso A D)
      (moduleResolutionDerivedTensorLeftFunctor A D S) (moduleResolutionDerivedTensorLeftFunctor
        A D T)
      (moduleResolutionDerivedTensorBifunctor A D S) (moduleResolutionDerivedTensorBifunctor A D T)
      (moduleResolutionDerivedTensorLeftIso A D S T).hom =
    Localization.liftNatTrans (leftModuleToDerived A D) (leftModuleQuasiIso A D)
      (moduleResolutionDerivedTensorLeftFunctor A D R) (moduleResolutionDerivedTensorLeftFunctor
        A D T)
      (moduleResolutionDerivedTensorBifunctor A D R) (moduleResolutionDerivedTensorBifunctor A D T)
      (moduleResolutionDerivedTensorLeftIso A D R T).hom
  rw [Localization.comp_liftNatTrans]
  exact congrArg (fun a => Localization.liftNatTrans (leftModuleToDerived A D)
    (leftModuleQuasiIso A D)
    (moduleResolutionDerivedTensorLeftFunctor A D R) (moduleResolutionDerivedTensorLeftFunctor A
      D T)
    (moduleResolutionDerivedTensorBifunctor A D R) (moduleResolutionDerivedTensorBifunctor A D T) a)
    (congrArg Iso.hom (moduleResolutionDerivedTensorLeftIso_trans A D R S T))


end SerrePositivity.DifferentialGraded
end

end TensorBifunctorChoice

/-! ## TensorResolutionComparison（旧 SerrePositivity/DifferentialGraded/Derived/TensorResolutionComparison.lean） -/

/-! # 任意解像度のtensor計算と左自然性・推移整合性 -/

@[expose] public section TensorResolutionComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end TensorResolutionComparison

/-! ## TensorComputationNaturality（旧 SerrePositivity/DifferentialGraded/Derived/TensorComputationNaturality.lean） -/

/-! # 導来tensor計算の射と解像度比較に関する自然性 -/

@[expose] public section TensorComputationNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleTensorHomotopyComputation_naturality (L : LeftModule A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (BalancedTensor.rightTensorHomotopyFunctor A D L).map ((moduleToHomotopy A D).map f) ≫
        (moduleTensorHomotopyComputation A D L N).hom =
      (moduleTensorHomotopyComputation A D L M).hom ≫
        (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map
          ((BalancedTensor.rightTensorFunctor A D L).map f) := by
  exact (eqToIso (BalancedTensor.rightTensorHomotopyFunctor_fac A D L)).hom.naturality f

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- K(D)上のtensorを、既存D(A)の具体的tensor値へ比較する。 -/
def moduleTensorDerivedHomotopyComputation (L : LeftModule A D) (M : ModuleCategory A D) :
    (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).obj
        ((moduleToHomotopy A D).obj M) ≅
      DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D L).obj M) :=
  DerivedCategory.Qh.mapIso (moduleTensorHomotopyComputation A D L M) ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app
      ((BalancedTensor.rightTensorFunctor A D L).obj M)

lemma moduleTensorDerivedHomotopyComputation_naturality (L : LeftModule A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).map
        ((moduleToHomotopy A D).map f) ≫
          (moduleTensorDerivedHomotopyComputation A D L N).hom =
      (moduleTensorDerivedHomotopyComputation A D L M).hom ≫
        DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map f) := by
  have h := congrArg (fun g => DerivedCategory.Qh.map g)
    (moduleTensorHomotopyComputation_naturality A D L f)
  simp only [CategoryTheory.Functor.map_comp] at h
  dsimp only [moduleTensorDerivedHomotopyComputation, Iso.trans_hom, Functor.mapIso_hom,
    Functor.comp_map, Iso.app_hom]
  rw [← Category.assoc, h, Category.assoc,
    DerivedCategory.quotientCompQhIso_hom_naturality, Category.assoc]

/-- 解像度族の比較自然同型は具体的な比較射によるtensor計算と可換。 -/
lemma moduleResolutionDerivedTensorComputation_choice
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModule A D) (M : ModuleCategory A D) :
    (moduleResolutionDerivedTensorIso A D R S L).hom.app ((moduleToDerived A D).obj M) ≫
        (moduleResolutionDerivedTensorComputation A D S L M).hom =
      (moduleResolutionDerivedTensorComputation A D R L M).hom ≫
        (moduleProjectiveResolutionTensorIso A D (R M) (S M) L).hom := by
  let H := BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh
  change H.map ((moduleDerivedResolutionIso A D R S).hom.app
      ((moduleToDerived A D).obj M)) ≫
      (H.map ((moduleDerivedResolutionComputation A D S M).hom) ≫
        (moduleTensorDerivedHomotopyComputation A D L (S M).obj).hom) =
    (H.map ((moduleDerivedResolutionComputation A D R M).hom) ≫
      (moduleTensorDerivedHomotopyComputation A D L (R M).obj).hom) ≫
        DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map
          ((R M).comparison (S M)))
  rw [moduleDerivedResolutionIso_hom_app]
  simp only [moduleDerivedResolutionComputation, moduleResolutionHomotopyIso_hom_app,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.app_hom]
  dsimp only [moduleResolutionHomotopyFunctor] at *
  rw [← Category.assoc (H.map ((moduleDerivedResolutionFunctor_fac A D S).inv.app M)),
    ← H.map_comp, Iso.inv_hom_id_app, H.map_id, Category.id_comp]
  exact congrArg (fun g => H.map ((moduleDerivedResolutionFunctor_fac A D R).hom.app M) ≫ g)
    (moduleTensorDerivedHomotopyComputation_naturality A D L ((R M).comparison (S M)))

end SerrePositivity.DifferentialGraded
end

end TensorComputationNaturality

/-! ## TensorBifunctorComputationChoice（旧 SerrePositivity/DifferentialGraded/Derived/TensorBifunctorComputationChoice.lean） -/

/-! # 両変数局所化の比較自然同型と具体的計算の可換図式 -/

@[expose] public section TensorBifunctorComputationChoice
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 局所化前の比較は、厳密な因子化で輸送した固定左加群の比較と一致する。 -/
lemma moduleResolutionDerivedTensorBifunctorIso_fac
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) :
    (moduleResolutionDerivedTensorBifunctorIso A D R S).hom.app
        ((leftModuleToDerived A D).obj L) ≫
          (eqToIso (moduleResolutionDerivedTensorBifunctor_obj A D S L)).hom =
      (eqToIso (moduleResolutionDerivedTensorBifunctor_obj A D R L)).hom ≫
        (moduleResolutionDerivedTensorIso A D R S (ForgetEnrichment.to (Complex A) L)).hom := by
  rw [moduleResolutionDerivedTensorBifunctorIso_hom_app]
  dsimp only [moduleResolutionDerivedTensorBifunctorFacIso, eqToIso]
  simp only [eqToHom_app, eqToHom_refl, Category.comp_id,
    moduleResolutionDerivedTensorLeftIso_hom_app]
  rfl

/-- 両変数導来tensorの解像度族変更は実際のtensor比較射による計算と可換。 -/
lemma moduleResolutionDerivedTensorBifunctorComputation_choice
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) (M : ModuleCategory A D) :
    ((moduleResolutionDerivedTensorBifunctorIso A D R S).hom.app
        ((leftModuleToDerived A D).obj L)).app ((moduleToDerived A D).obj M) ≫
        (moduleResolutionDerivedTensorBifunctorComputation A D S L M).hom =
      (moduleResolutionDerivedTensorBifunctorComputation A D R L M).hom ≫
        (moduleProjectiveResolutionTensorIso A D (R M) (S M)
          (ForgetEnrichment.to (Complex A) L)).hom := by
  have h := NatTrans.congr_app (moduleResolutionDerivedTensorBifunctorIso_fac A D R S L)
    ((moduleToDerived A D).obj M)
  simp only [NatTrans.comp_app] at h
  dsimp only [moduleResolutionDerivedTensorBifunctorComputation, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, h, Category.assoc,
    moduleResolutionDerivedTensorComputation_choice, ← Category.assoc]

/-- 任意の個別解像度で計算すると、解像度族変更はその同じ計算値で一致する。 -/
lemma moduleTensorBifunctorResolutionComputation_choice
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) :
    ((moduleResolutionDerivedTensorBifunctorIso A D R S).hom.app
        ((leftModuleToDerived A D).obj L)).app ((moduleToDerived A D).obj M) ≫
        (moduleTensorBifunctorResolutionComputation A D S L P).hom =
      (moduleTensorBifunctorResolutionComputation A D R L P).hom := by
  dsimp only [moduleTensorBifunctorResolutionComputation, Iso.trans_hom]
  rw [← Category.assoc, moduleResolutionDerivedTensorBifunctorComputation_choice,
    Category.assoc, ← Iso.trans_hom, moduleProjectiveResolutionTensorIso_trans]

end SerrePositivity.DifferentialGraded
end

end TensorBifunctorComputationChoice
