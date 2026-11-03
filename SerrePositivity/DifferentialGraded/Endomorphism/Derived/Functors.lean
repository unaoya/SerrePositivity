module

public import SerrePositivity.DifferentialGraded.Endomorphism.Module
public import SerrePositivity.DifferentialGraded.Derived.Projective

public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
public import SerrePositivity.DifferentialGraded.Derived.Tensor
public import SerrePositivity.DifferentialGraded.Derived.Basic

public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration

/-!
# Endomorphism.Derived.Functors

## 概要
再構成 Hom・tensor の導来化、評価と局所生成判定をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## DerivedHom（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedHom.lean） -/

/-! # 指定射影的dg加群からのHomの導来化

Eのホモトピー射影性を明示し、Hom(E,−)が擬同型を保つことから指定局所化へ降ろす。
-/

@[expose] public section DerivedHom
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- Hom関手の閉零成分は主Hom endの後合成射に等しい。 -/
lemma endomorphismModuleHom_map_eval (M M' : RightModule A D)
    (f : ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) M')
    (b : EndomorphismObject E) :
    (moduleEvaluation A (EndomorphismObject E) b).map
      ((endomorphismModuleHom A D E).onClosed.map f) =
    eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) E) f := by
  cases b
  apply HomologicalComplex.hom_ext
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply moduleHomElement_ext A D
  intro d
  apply Cochain.ext
  intro s n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  have h := congrArg (fun k => (k.f r m).v s n hn t)
    (moduleHomWhiskerLeft_π A D (M := ForgetEnrichment.of (Complex A) E) f d)
  change ((moduleHomπ A D E M' d).f r
      ((eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) E) f).f r m)).v s n hn t =
    ((homPostcompose (E.obj (op d)) ((moduleEvaluation A D d).map f)).f r
      ((moduleHomπ A D E M d).f r m)).v s n hn t at h
  rw [homPostcompose_apply, Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at h
  exact (endomorphismModuleHom_map_eval_apply A D E M M' f d m t hn).trans h.symm

/-- Eのホモトピー射影性の下でHom(E,−)は指定擬同型を保つ。 -/
lemma endomorphismModuleHom_quasiIso
    (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))
    {M M' : ModuleCategory A D} (f : M ⟶ M') (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A (EndomorphismObject E) ((endomorphismModuleHom A D E).onClosed.map f) := by
  intro b
  rw [endomorphismModuleHom_map_eval]
  exact moduleHomotopicallyProjective_postcompose_quasiIso A D hE f hf

/-- 局所化後のHom関手は、元の指定擬同型を反転する。 -/
lemma endomorphismModuleHomToDerived_inverts
    (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E)) :
    (moduleQuasiIso A D).IsInvertedBy
      ((endomorphismModuleHom A D E).onClosed ⋙ moduleToDerived A (EndomorphismObject E)) :=
  fun _ _ f hf => moduleToDerived_inverts A (EndomorphismObject E) _
    (endomorphismModuleHom_quasiIso A D E hE f hf)

/-- 射影的指定対象のHomを主導来加群圏間の関手へ降ろす。 -/
def endomorphismDerivedHom
    (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E)) :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A (EndomorphismObject E) :=
  moduleDerivedLift A D
    ((endomorphismModuleHom A D E).onClosed ⋙ moduleToDerived A (EndomorphismObject E))
    (endomorphismModuleHomToDerived_inverts A D E hE)

/-- 導来Homの構成は指定局所化との厳密な可換式を持つ。 -/
lemma endomorphismDerivedHom_fac
    (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E)) :
    moduleToDerived A D ⋙ endomorphismDerivedHom A D E hE =
      (endomorphismModuleHom A D E).onClosed ⋙ moduleToDerived A (EndomorphismObject E) :=
  moduleDerivedLift_fac A D _ _

/-- U13のperfect dg代表に保持された射影性を使う導来Hom。 -/
def perfectEndomorphismDerivedHom (S : Set D) (E : PerfectDGModuleOver A D S) :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A (EndomorphismObject E.val) :=
  endomorphismDerivedHom A D E.val E.property.1

end SerrePositivity.DifferentialGraded
end

end DerivedHom

/-! ## DerivedTensor（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedTensor.lean） -/

/-! # 指定dg加群Eとの再構成tensorの導来化

右End(E)加群を射影解像し、主Kを通じてD(D)へ送る。
Eの成分のA-flat性や全加群dg圏の対象型のsmall性は仮定しない。
-/

@[expose] public section DerivedTensor
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 任意の右End(E)射影解像度族で構成する再構成導来tensor。 -/
def endomorphismResolutionDerivedTensor
    (R : ∀ N : ModuleCategory A (EndomorphismObject E),
      ModuleProjectiveResolution A (EndomorphismObject E) N) :
    DerivedModuleCategory A (EndomorphismObject E) ⥤ DerivedModuleCategory A D :=
  moduleDerivedResolutionFunctor A (EndomorphismObject E) R ⋙
    (endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D

/-- 主semifree射影解像度から作る再構成導来tensor。 -/
def endomorphismDerivedTensor :
    DerivedModuleCategory A (EndomorphismObject E) ⥤ DerivedModuleCategory A D :=
  endomorphismResolutionDerivedTensor A D E
    (moduleCanonicalProjectiveResolution A (EndomorphismObject E))

/-- 実際のdg tensor関手とH⁰関手の対象比較。 -/
def endomorphismTensorHomotopyComputation (N : ModuleCategory A (EndomorphismObject E)) :
    (endomorphismModuleTensor A D E).onHomotopy.obj
      ((moduleToHomotopy A (EndomorphismObject E)).obj N) ≅
    (moduleToHomotopy A D).obj ((endomorphismModuleTensor A D E).onClosed.obj N) :=
  eqToIso (congrArg (fun F => F.obj N) (endomorphismModuleTensor A D E).onHomotopy_fac)

/-- 指定局所化の対象での、選んだ射影解像度による実際の計算同型。 -/
def endomorphismResolutionDerivedTensorComputation
    (R : ∀ N : ModuleCategory A (EndomorphismObject E),
      ModuleProjectiveResolution A (EndomorphismObject E) N)
    (N : ModuleCategory A (EndomorphismObject E)) :
    (endomorphismResolutionDerivedTensor A D E R).obj
        ((moduleToDerived A (EndomorphismObject E)).obj N) ≅
      (moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj (R N).obj) :=
  ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D).mapIso
      (moduleDerivedResolutionComputation A (EndomorphismObject E) R N) ≪≫
    (moduleHomotopyToDerivedClosed A D).mapIso
      (endomorphismTensorHomotopyComputation A D E (R N).obj) ≪≫
    (moduleToHomotopyDerivedIso A D).app ((endomorphismModuleTensor A D E).onClosed.obj (R N).obj)

/-- 任意の二つの射影解像度族を用いた導来tensorの自然な比較。 -/
def endomorphismResolutionDerivedTensorIso
    (R S : ∀ N : ModuleCategory A (EndomorphismObject E),
      ModuleProjectiveResolution A (EndomorphismObject E) N) :
    endomorphismResolutionDerivedTensor A D E R ≅ endomorphismResolutionDerivedTensor A D E S :=
  Functor.isoWhiskerRight (moduleDerivedResolutionIso A (EndomorphismObject E) R S)
    ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D)

lemma endomorphismResolutionDerivedTensorIso_self
    (R : ∀ N : ModuleCategory A (EndomorphismObject E),
      ModuleProjectiveResolution A (EndomorphismObject E) N) :
    endomorphismResolutionDerivedTensorIso A D E R R = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D).map
    ((moduleDerivedResolutionIso A (EndomorphismObject E) R R).hom.app X) = 𝟙 _
  rw [moduleDerivedResolutionIso_self]
  exact ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D).map_id _

lemma endomorphismResolutionDerivedTensorIso_trans
    (R S T : ∀ N : ModuleCategory A (EndomorphismObject E),
      ModuleProjectiveResolution A (EndomorphismObject E) N) :
    endomorphismResolutionDerivedTensorIso A D E R S ≪≫
      endomorphismResolutionDerivedTensorIso A D E S T =
        endomorphismResolutionDerivedTensorIso A D E R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D).map
      ((moduleDerivedResolutionIso A (EndomorphismObject E) R S).hom.app X) ≫
    ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D).map
      ((moduleDerivedResolutionIso A (EndomorphismObject E) S T).hom.app X) = _
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun f =>
    ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D).map f)
    (NatTrans.congr_app (congrArg Iso.hom
      (moduleDerivedResolutionIso_trans A (EndomorphismObject E) R S T)) X)

/-- 射影的右加群間の擬同型をtensorすると擬同型。Eの成分のflat性は不要。 -/
lemma endomorphismModuleTensor_projective_quasiIso
    {N N' : ModuleCategory A (EndomorphismObject E)}
    (hN : moduleHomotopicallyProjective A (EndomorphismObject E) N)
    (hN' : moduleHomotopicallyProjective A (EndomorphismObject E) N')
    (f : N ⟶ N') (hf : moduleQuasiIso A (EndomorphismObject E) f) :
    moduleQuasiIso A D ((endomorphismModuleTensor A D E).onClosed.map f) := by
  intro d
  rw [endomorphismModuleTensor_map_eval]
  exact BalancedTensor.rightTensor_projective_quasiIso A (EndomorphismObject E)
    ((endomorphismModuleAction A D E).leftAt d) hN hN' f hf

/-- 同じK射を表す閉零射は再構成tensor後の主導来圏でも同じ射となる。 -/
lemma endomorphismTensorDerived_map_eq_of_homotopy_map_eq
    {N N' : ModuleCategory A (EndomorphismObject E)} {f g : N ⟶ N'}
    (h : (moduleToHomotopy A (EndomorphismObject E)).map f =
      (moduleToHomotopy A (EndomorphismObject E)).map g) :
    (moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map f) =
      (moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map g) :=
  moduleQuasiIso_equalizes_boundary A D (moduleToDerived A D) (moduleToDerived_inverts A D) _ _
    ((endomorphismModuleTensor A D E).preserves_boundary f g
      ((toHomotopy_map_eq_iff A (RightModule A (EndomorphismObject E)) f g).mp h))

/-- 二つの任意射影解像度による実際のtensor計算の同型。 -/
def endomorphismProjectiveResolutionTensorIso
    {N : ModuleCategory A (EndomorphismObject E)}
    (P Q : ModuleProjectiveResolution A (EndomorphismObject E) N) :
    (moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj P.obj) ≅
      (moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj Q.obj) := by
  letI := moduleToDerived_inverts A D _
    (endomorphismModuleTensor_projective_quasiIso A D E P.projective Q.projective
      (P.comparison Q) (P.comparison_quasiIso Q))
  exact asIso ((moduleToDerived A D).map
    ((endomorphismModuleTensor A D E).onClosed.map (P.comparison Q)))

lemma endomorphismProjectiveResolutionTensorIso_hom
    {N : ModuleCategory A (EndomorphismObject E)}
    (P Q : ModuleProjectiveResolution A (EndomorphismObject E) N) :
    (endomorphismProjectiveResolutionTensorIso A D E P Q).hom =
      (moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map (P.comparison Q)) :=
  rfl

lemma endomorphismProjectiveResolutionTensorIso_self
    {N : ModuleCategory A (EndomorphismObject E)}
    (P : ModuleProjectiveResolution A (EndomorphismObject E) N) :
    endomorphismProjectiveResolutionTensorIso A D E P P = Iso.refl _ := by
  apply Iso.ext
  change (moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map
    (P.comparison P)) = 𝟙 _
  have h := endomorphismTensorDerived_map_eq_of_homotopy_map_eq A D E
    (P.comparison_self.trans ((moduleToHomotopy A (EndomorphismObject E)).map_id P.obj).symm)
  simpa only [CategoryTheory.Functor.map_id] using h

lemma endomorphismProjectiveResolutionTensorIso_trans
    {N : ModuleCategory A (EndomorphismObject E)}
    (P Q R : ModuleProjectiveResolution A (EndomorphismObject E) N) :
    endomorphismProjectiveResolutionTensorIso A D E P Q ≪≫
      endomorphismProjectiveResolutionTensorIso A D E Q R =
        endomorphismProjectiveResolutionTensorIso A D E P R := by
  apply Iso.ext
  change (moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map
      (P.comparison Q)) ≫
    (moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map (Q.comparison R)) = _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact endomorphismTensorDerived_map_eq_of_homotopy_map_eq A D E
    (((moduleToHomotopy A (EndomorphismObject E)).map_comp (P.comparison Q) (Q.comparison R)).trans
      (P.comparison_comp Q R))

/-- 標準の導来tensorは任意の右End(E)射影解像度で計算できる。 -/
def endomorphismDerivedTensorResolutionComputation
    {N : ModuleCategory A (EndomorphismObject E)}
    (P : ModuleProjectiveResolution A (EndomorphismObject E) N) :
    (endomorphismDerivedTensor A D E).obj ((moduleToDerived A (EndomorphismObject E)).obj N) ≅
      (moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj P.obj) :=
  endomorphismResolutionDerivedTensorComputation A D E
      (moduleCanonicalProjectiveResolution A (EndomorphismObject E)) N ≪≫
    endomorphismProjectiveResolutionTensorIso A D E
      (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N) P

end SerrePositivity.DifferentialGraded
end

end DerivedTensor

/-! ## DerivedTensorNaturality（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedTensorNaturality.lean） -/

/-! # 解像度による再構成導来tensor計算の自然性 -/

@[expose] public section DerivedTensorNaturality
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

lemma endomorphismResolutionDerivedTensorComputation_naturality
    (R : ∀ N : ModuleCategory A (EndomorphismObject E),
      ModuleProjectiveResolution A (EndomorphismObject E) N)
    {N N' : ModuleCategory A (EndomorphismObject E)} (f : N ⟶ N') :
    (endomorphismResolutionDerivedTensor A D E R).map
        ((moduleToDerived A (EndomorphismObject E)).map f) ≫
        (endomorphismResolutionDerivedTensorComputation A D E R N').hom =
      (endomorphismResolutionDerivedTensorComputation A D E R N).hom ≫
        (moduleToDerived A D).map
          ((endomorphismModuleTensor A D E).onClosed.map ((R N).lift (R N') f)) := by
  let H := (endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D
  have h₁ := congrArg H.map
    ((moduleDerivedResolutionFunctor_fac A (EndomorphismObject E) R).hom.naturality f)
  simp only [Functor.map_comp] at h₁
  have h₂ := congrArg (moduleHomotopyToDerivedClosed A D).map
    ((eqToIso (endomorphismModuleTensor A D E).onHomotopy_fac).hom.naturality
      ((R N).lift (R N') f))
  simp only [Functor.map_comp] at h₂
  have h₃ := (moduleToHomotopyDerivedIso A D).hom.naturality
    ((endomorphismModuleTensor A D E).onClosed.map ((R N).lift (R N') f))
  change H.map ((moduleDerivedResolutionFunctor A (EndomorphismObject E) R).map
      ((moduleToDerived A (EndomorphismObject E)).map f)) ≫
      H.map (moduleDerivedResolutionComputation A (EndomorphismObject E) R N').hom =
    H.map (moduleDerivedResolutionComputation A (EndomorphismObject E) R N).hom ≫
      H.map ((moduleToHomotopy A (EndomorphismObject E)).map ((R N).lift (R N') f)) at h₁
  change H.map ((moduleToHomotopy A (EndomorphismObject E)).map ((R N).lift (R N') f)) ≫
      (moduleHomotopyToDerivedClosed A D).map
        (endomorphismTensorHomotopyComputation A D E (R N').obj).hom =
    (moduleHomotopyToDerivedClosed A D).map
        (endomorphismTensorHomotopyComputation A D E (R N).obj).hom ≫
      (moduleHomotopyToDerivedClosed A D).map
        ((moduleToHomotopy A D).map
          ((endomorphismModuleTensor A D E).onClosed.map ((R N).lift (R N') f))) at h₂
  change (moduleHomotopyToDerivedClosed A D).map
      ((moduleToHomotopy A D).map
        ((endomorphismModuleTensor A D E).onClosed.map ((R N).lift (R N') f))) ≫
      ((moduleToHomotopyDerivedIso A D).app
        ((endomorphismModuleTensor A D E).onClosed.obj (R N').obj)).hom =
    ((moduleToHomotopyDerivedIso A D).app
        ((endomorphismModuleTensor A D E).onClosed.obj (R N).obj)).hom ≫
      (moduleToDerived A D).map
        ((endomorphismModuleTensor A D E).onClosed.map ((R N).lift (R N') f)) at h₃
  change H.map _ ≫ (H.map _ ≫ _ ≫ _) = (H.map _ ≫ _ ≫ _) ≫ _
  rw [← Category.assoc, h₁]
  simp only [Category.assoc]
  apply congrArg (fun t => H.map
    (moduleDerivedResolutionComputation A (EndomorphismObject E) R N).hom ≫ t)
  have h₄ := congrArg
    (fun t => t ≫ (moduleToHomotopyDerivedIso A D).hom.app
      ((endomorphismModuleTensor A D E).onClosed.obj (R N').obj)) h₂
  have h₅ := congrArg
    (fun t => (moduleHomotopyToDerivedClosed A D).map
      (endomorphismTensorHomotopyComputation A D E (R N).obj).hom ≫ t) h₃
  simp only [Category.assoc] at h₄ h₅
  have h₆ := h₄.trans h₅
  exact h₆

lemma endomorphismDerivedTensorResolutionComputation_canonical
    (N : ModuleCategory A (EndomorphismObject E)) :
    endomorphismDerivedTensorResolutionComputation A D E
        (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N) =
      endomorphismResolutionDerivedTensorComputation A D E
        (moduleCanonicalProjectiveResolution A (EndomorphismObject E)) N := by
  simp [endomorphismDerivedTensorResolutionComputation,
    endomorphismProjectiveResolutionTensorIso_self]

lemma endomorphismDerivedTensorResolutionComputation_inv_naturality
    {N N' : ModuleCategory A (EndomorphismObject E)} (f : N ⟶ N') :
    (endomorphismDerivedTensorResolutionComputation A D E
        (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N)).inv ≫
        (endomorphismDerivedTensor A D E).map
          ((moduleToDerived A (EndomorphismObject E)).map f) =
      (moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map
        ((moduleCanonicalProjectiveResolution A (EndomorphismObject E) N).lift
          (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N') f)) ≫
        (endomorphismDerivedTensorResolutionComputation A D E
          (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N')).inv := by
  rw [endomorphismDerivedTensorResolutionComputation_canonical,
    endomorphismDerivedTensorResolutionComputation_canonical]
  dsimp only [endomorphismDerivedTensor]
  have h := endomorphismResolutionDerivedTensorComputation_naturality A D E
    (moduleCanonicalProjectiveResolution A (EndomorphismObject E)) f
  apply (cancel_mono (endomorphismResolutionDerivedTensorComputation A D E
    (moduleCanonicalProjectiveResolution A (EndomorphismObject E)) N').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

end SerrePositivity.DifferentialGraded
end

end DerivedTensorNaturality

/-! ## DerivedTensorEvaluation（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedTensorEvaluation.lean） -/

/-! # 再構成導来tensorの各D成分とU12dの導来tensorの自然比較

関手間の自然同型として比較し、対象での計算だけには留めない。
-/

@[expose] public section DerivedTensorEvaluation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 再構成tensorの各D成分はU11のbalanced tensor関手と自然に一致する。 -/
def endomorphismTensorEvaluationIso (d : D) :
    (endomorphismModuleTensor A D E).onClosed ⋙ moduleEvaluation A D d ≅
      BalancedTensor.rightTensorFunctor A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    change (moduleEvaluation A D d).map ((endomorphismModuleTensor A D E).onClosed.map f) ≫ 𝟙 _ =
      𝟙 _ ≫ BalancedTensor.rightTensorMap A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) f
    rw [Category.comp_id, Category.id_comp]
    exact endomorphismModuleTensor_map_eval A D E f d)

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- K(End(E))上の再構成tensor評価を、閉零代表上でbalanced tensorと比較する。 -/
def endomorphismTensorHomotopyEvaluationFacIso (d : D) :
    moduleToHomotopy A (EndomorphismObject E) ⋙
        (endomorphismModuleTensor A D E).onHomotopy ⋙
          moduleHomotopyToDerivedClosed A D ⋙ moduleDerivedEvaluation A D d ≅
      BalancedTensor.rightTensorFunctor A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) ⋙ DerivedCategory.Q :=
  (Functor.associator (moduleToHomotopy A (EndomorphismObject E))
    (endomorphismModuleTensor A D E).onHomotopy
    (moduleHomotopyToDerivedClosed A D ⋙ moduleDerivedEvaluation A D d)).symm ≪≫
  Functor.isoWhiskerRight (eqToIso (endomorphismModuleTensor A D E).onHomotopy_fac)
    (moduleHomotopyToDerivedClosed A D ⋙ moduleDerivedEvaluation A D d) ≪≫
  Functor.associator (endomorphismModuleTensor A D E).onClosed (moduleToHomotopy A D)
    (moduleHomotopyToDerivedClosed A D ⋙ moduleDerivedEvaluation A D d) ≪≫
  Functor.isoWhiskerLeft (endomorphismModuleTensor A D E).onClosed
    ((Functor.associator (moduleToHomotopy A D) (moduleHomotopyToDerivedClosed A D)
      (moduleDerivedEvaluation A D d)).symm ≪≫ moduleDerivedEvaluationHomotopyFacIso A D d) ≪≫
  (Functor.associator (endomorphismModuleTensor A D E).onClosed (moduleEvaluation A D d)
    DerivedCategory.Q).symm ≪≫
  Functor.isoWhiskerRight (endomorphismTensorEvaluationIso A D E d) DerivedCategory.Q

/-- U12dのhomotopy tensorを、閉零代表上で同じbalanced tensorへ比較する。 -/
def endomorphismU12dHomotopyTensorFacIso (d : D) :
    moduleToHomotopy A (EndomorphismObject E) ⋙
        BalancedTensor.rightTensorHomotopyFunctor A (EndomorphismObject E)
          ((endomorphismModuleAction A D E).leftAt d) ⋙ DerivedCategory.Qh ≅
      BalancedTensor.rightTensorFunctor A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) ⋙ DerivedCategory.Q :=
  (Functor.associator (moduleToHomotopy A (EndomorphismObject E))
    (BalancedTensor.rightTensorHomotopyFunctor A (EndomorphismObject E)
      ((endomorphismModuleAction A D E).leftAt d)) DerivedCategory.Qh).symm ≪≫
  Functor.isoWhiskerRight
    (eqToIso (BalancedTensor.rightTensorHomotopyFunctor_fac A (EndomorphismObject E)
      ((endomorphismModuleAction A D E).leftAt d))) DerivedCategory.Qh ≪≫
  Functor.associator
    (BalancedTensor.rightTensorFunctor A (EndomorphismObject E)
      ((endomorphismModuleAction A D E).leftAt d))
    (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)) DerivedCategory.Qh ≪≫
  Functor.isoWhiskerLeft
    (BalancedTensor.rightTensorFunctor A (EndomorphismObject E)
      ((endomorphismModuleAction A D E).leftAt d))
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A))

/-- 全てのK(End(E))射に自然な、再構成tensor評価とU12dの比較。 -/
def endomorphismTensorHomotopyEvaluationIso (d : D) :
    (endomorphismModuleTensor A D E).onHomotopy ⋙
        moduleHomotopyToDerivedClosed A D ⋙ moduleDerivedEvaluation A D d ≅
      BalancedTensor.rightTensorHomotopyFunctor A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) ⋙ DerivedCategory.Qh :=
  Quotient.natIsoLift (boundaryRelation A (RightModule A (EndomorphismObject E)))
    (endomorphismTensorHomotopyEvaluationFacIso A D E d ≪≫
      (endomorphismU12dHomotopyTensorFacIso A D E d).symm)

/-- 任意の右射影解像度族について、導来tensorのD評価はU12dの導来tensorと自然同型。 -/
def endomorphismResolutionDerivedTensorEvaluationIso
    (R : ∀ N : ModuleCategory A (EndomorphismObject E),
      ModuleProjectiveResolution A (EndomorphismObject E) N) (d : D) :
    endomorphismResolutionDerivedTensor A D E R ⋙ moduleDerivedEvaluation A D d ≅
      moduleResolutionDerivedTensor A (EndomorphismObject E) R
        ((endomorphismModuleAction A D E).leftAt d) :=
  Functor.associator (moduleDerivedResolutionFunctor A (EndomorphismObject E) R)
    ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D)
    (moduleDerivedEvaluation A D d) ≪≫
  Functor.isoWhiskerLeft (moduleDerivedResolutionFunctor A (EndomorphismObject E) R)
    (Functor.associator (endomorphismModuleTensor A D E).onHomotopy
      (moduleHomotopyToDerivedClosed A D) (moduleDerivedEvaluation A D d) ≪≫
        endomorphismTensorHomotopyEvaluationIso A D E d)

/-- 主再構成導来tensorと既存U12d導来tensorの自然な評価正方形。 -/
def endomorphismDerivedTensorEvaluationIso (d : D) :
    endomorphismDerivedTensor A D E ⋙ moduleDerivedEvaluation A D d ≅
      moduleDerivedTensorRight A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) :=
  endomorphismResolutionDerivedTensorEvaluationIso A D E
    (moduleCanonicalProjectiveResolution A (EndomorphismObject E)) d

end SerrePositivity.DifferentialGraded
end

end DerivedTensorEvaluation

/-! ## DerivedEvaluation（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedEvaluation.lean） -/

/-! # U12dの導来tensorからの指定対象を通る評価

解像度のaugmentationを使って評価を定義する。同型性はここでは主張しない。
-/

@[expose] public section DerivedEvaluation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (E X Y : D)

/-- 解像度の実際のaugmentationを合成するchain-level評価。 -/
def endomorphismResolutionEvaluation
    (P : ModuleProjectiveResolution A (EndomorphismObject E)
      (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y))) :
    (BalancedTensor.rightTensorFunctor A _ (endomorphismHomLeft A D E X)).obj P.obj ⟶
      homObject A D X Y :=
  (BalancedTensor.rightTensorFunctor A _ (endomorphismHomLeft A D E X)).map P.π ≫
    endomorphismEvaluation A D E X Y

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- augmentationの因子化はホモトピーまで成立するため、評価の正方形は導来圏で可換。 -/
lemma endomorphismResolutionEvaluation_comparison
    (P Q : ModuleProjectiveResolution A (EndomorphismObject E)
      (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y))) :
    DerivedCategory.Q.map
      ((BalancedTensor.rightTensorFunctor A _ (endomorphismHomLeft A D E X)).map
        (P.comparison Q)) ≫
        DerivedCategory.Q.map (endomorphismResolutionEvaluation A D E X Y Q) =
      DerivedCategory.Q.map (endomorphismResolutionEvaluation A D E X Y P) := by
  have h := moduleTensorDerived_map_eq_of_homotopy_map_eq A (EndomorphismObject E)
    (endomorphismHomLeft A D E X)
    (((moduleToHomotopy A (EndomorphismObject E)).map_comp (P.comparison Q) Q.π).trans
      (P.comparison_fac Q))
  dsimp only [endomorphismResolutionEvaluation]
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
    congrArg (fun f => f ≫ DerivedCategory.Q.map (endomorphismEvaluation A D E X Y)) h

/-- U12dの既存導来tensorを標準解像度で計算して得る評価。 -/
def endomorphismDerivedEvaluation :
    (moduleDerivedTensorRight A (EndomorphismObject E) (endomorphismHomLeft A D E X)).obj
        ((moduleToDerived A (EndomorphismObject E)).obj
          (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y))) ⟶
      DerivedCategory.Q.obj (homObject A D X Y) :=
  (moduleResolutionDerivedTensorComputation A (EndomorphismObject E)
      (moduleCanonicalProjectiveResolution A (EndomorphismObject E))
      (endomorphismHomLeft A D E X)
      (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y))).hom ≫
    DerivedCategory.Q.map (endomorphismResolutionEvaluation A D E X Y
      (moduleCanonicalProjectiveResolution A (EndomorphismObject E)
        (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y))))

/-- 任意の射影解像度による計算でも同じ導来評価になる。 -/
lemma endomorphismDerivedEvaluation_resolution
    (P : ModuleProjectiveResolution A (EndomorphismObject E)
      (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y))) :
    (moduleDerivedTensorRightResolutionComputation A (EndomorphismObject E) P
      (endomorphismHomLeft A D E X)).hom ≫
        DerivedCategory.Q.map (endomorphismResolutionEvaluation A D E X Y P) =
      endomorphismDerivedEvaluation A D E X Y := by
  simp only [moduleDerivedTensorRightResolutionComputation, Iso.trans_hom,
    Category.assoc, moduleProjectiveResolutionTensorIso_hom,
    endomorphismResolutionEvaluation_comparison, endomorphismDerivedEvaluation]

end SerrePositivity.DifferentialGraded
end

end DerivedEvaluation

/-! ## DerivedScalarTensor（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedScalarTensor.lean） -/

/-! # 再構成導来tensorの評価と導来係数変更

係数変更側の受入済みAPIのK-flat計算条件を明示して使う。
係数変更したEnd(E)をEnd(係数変更したE)と同一視する主張は含まない。
-/

@[expose] public section DerivedScalarTensor
universe u v w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D] (E : RightModule A D)
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

/-- 再構成tensorの評価・U12d比較を経由した導来係数変更同型。 -/
def endomorphismDerivedTensorBaseChange (d : D)
    {N : ModuleCategory A (EndomorphismObject E)}
    (P : ModuleProjectiveResolution A (EndomorphismObject E) N)
    (hPN : complexKFlat A (BalancedTensor.obj A (EndomorphismObject E)
      (ForgetEnrichment.to (Complex A) P.obj) ((endomorphismModuleAction A D E).leftAt d)))
    (hP' : moduleRelativeKFlat A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
      (ScalarExtension.rightModule φ (EndomorphismObject E)
        (ForgetEnrichment.to (Complex A) P.obj))) :
    (ScalarExtension.complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A D d).obj ((endomorphismDerivedTensor A D E).obj
          ((moduleToDerived A (EndomorphismObject E)).obj N))) ≅
      (moduleDerivedTensorRight A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
        (ScalarExtension.leftModule φ (EndomorphismObject E)
          ((endomorphismModuleAction A D E).leftAt d))).obj
        ((ScalarExtension.derivedExtension φ (EndomorphismObject E)).obj
          ((moduleToDerived A (EndomorphismObject E)).obj N)) :=
  (ScalarExtension.complexDerivedExtension φ).mapIso
    ((endomorphismDerivedTensorEvaluationIso A D E d).app
      ((moduleToDerived A (EndomorphismObject E)).obj N)) ≪≫
    ScalarExtension.derivedTensorBaseChange φ (EndomorphismObject E) P
      ((endomorphismModuleAction A D E).leftAt d) hPN hP'

/-- 上の計算同型は既存U12d比較と係数変更比較の正方形を与える。 -/
lemma endomorphismDerivedTensorBaseChange_square (d : D)
    {N : ModuleCategory A (EndomorphismObject E)}
    (P : ModuleProjectiveResolution A (EndomorphismObject E) N)
    (hPN : complexKFlat A (BalancedTensor.obj A (EndomorphismObject E)
      (ForgetEnrichment.to (Complex A) P.obj) ((endomorphismModuleAction A D E).leftAt d)))
    (hP' : moduleRelativeKFlat A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
      (ScalarExtension.rightModule φ (EndomorphismObject E)
        (ForgetEnrichment.to (Complex A) P.obj))) :
    (endomorphismDerivedTensorBaseChange φ D E d P hPN hP').hom =
      (ScalarExtension.complexDerivedExtension φ).map
        ((endomorphismDerivedTensorEvaluationIso A D E d).hom.app
          ((moduleToDerived A (EndomorphismObject E)).obj N)) ≫
      (ScalarExtension.derivedTensorBaseChange φ (EndomorphismObject E) P
        ((endomorphismModuleAction A D E).leftAt d) hPN hP').hom := rfl

/-- 再構成tensor評価とU12d比較の係数変更後の全導来射自然性。 -/
lemma endomorphismDerivedTensorEvaluationScalar_naturality (d : D)
    {X Y : DerivedModuleCategory A (EndomorphismObject E)} (f : X ⟶ Y) :
    (ScalarExtension.complexDerivedExtension φ).map
        ((endomorphismDerivedTensor A D E ⋙ moduleDerivedEvaluation A D d).map f) ≫
      (ScalarExtension.complexDerivedExtension φ).map
        ((endomorphismDerivedTensorEvaluationIso A D E d).hom.app Y) =
    (ScalarExtension.complexDerivedExtension φ).map
        ((endomorphismDerivedTensorEvaluationIso A D E d).hom.app X) ≫
      (ScalarExtension.complexDerivedExtension φ).map
        ((moduleDerivedTensorRight A (EndomorphismObject E)
          ((endomorphismModuleAction A D E).leftAt d)).map f) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (ScalarExtension.complexDerivedExtension φ).map
    ((endomorphismDerivedTensorEvaluationIso A D E d).hom.naturality f)

end SerrePositivity.DifferentialGraded
end

end DerivedScalarTensor

/-! ## DerivedLocalizingGeneration（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedLocalizingGeneration.lean） -/

/-! # 全主導来対象を余積とconeで生成するための判定

既存の標準解像度とtelescope coneの擬同型を用いる。
compact⇒Perfの再証明ではなく、余積閉な三角部分圏への全対象の所属を扱う。
-/

@[expose] public section DerivedLocalizingGeneration
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : ObjectProperty (DerivedModuleCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
variable (hcop : ∀ (J : Type u) (F : J → DerivedModuleCategory A D),
  (∀ j, P (F j)) → P (∐ F))
variable (hperf : ∀ X : DerivedModuleCategory A D, modulePerfect A D X → P X)
include hcop

omit [P.IsTriangulated] in
lemma moduleLocalizing_projectiveCoproduct {J : Type w} [Small.{u} J]
    (M : J → ModuleCategory A D) (hM : ∀ j, moduleHomotopicallyProjective A D (M j))
    (hF : ∀ j, P ((moduleToDerived A D).obj (M j))) :
    P ((moduleToDerived A D).obj (∐ M)) := by
  let F := fun j => (moduleToDerived A D).obj (M j)
  have hc : P (∐ F) := by
    let e : Shrink.{u} J ≃ J := (equivShrink J).symm
    exact P.prop_of_iso (Sigma.reindex e F) (hcop _ (F ∘ e) (fun j => hF (e j)))
  exact P.prop_of_iso
    ((colimit.isColimit (Discrete.functor F)).coconePointUniqueUpToIso
      (moduleProjectiveDerivedCofanIsColimit A D M hM)) hc

include hperf

omit [P.IsTriangulated] in
lemma moduleLocalizing_sphereCoproduct {J : Type w} [Small.{u} J]
    (x : J → D) (n : J → ℤ) :
    P ((moduleToDerived A D).obj (∐ fun j => freeSphere A D (x j) (n j))) := by
  apply moduleLocalizing_projectiveCoproduct A D P hcop _
    (fun j => freeSphere_homotopicallyProjective A D (x j) (n j))
  intro j
  apply hperf
  exact modulePerfectOver_of_finiteCell A D
    (moduleFiniteCellOver_freeSphere A D (x j) (Set.mem_univ _) (n j))

lemma moduleLocalizing_resolutionStage (M : ModuleCategory A D) (n : ℕ) :
    P ((moduleToDerived A D).obj (moduleResolutionStage A D M n).left) := by
  induction n with
  | zero =>
    apply P.prop_of_isZero
    apply moduleToDerived_isZero_of_acyclic A D
    intro x i
    let : HasExactColimitsOfShape (Discrete (ModuleDiskCoverIndex A D M)) (ModuleCat.{u} A) :=
      HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
        (Discrete.equivalence (equivShrink.{u} (ModuleDiskCoverIndex A D M)).symm)
    exact (complex_colimit_acyclic A
      (Discrete.functor (moduleDiskCoverFamily A D M) ⋙ moduleEvaluation A D x)
      (fun j => freeDisk_acyclic A D j.as.1 j.as.2.1 x) i).of_iso
        (preservesColimitIso (moduleEvaluation A D x)
          (Discrete.functor (moduleDiskCoverFamily A D M))).symm
  | succ n ih =>
    exact P.ext_of_isTriangulatedClosed₃ _
      (moduleDerivedConeTriangle_distinguished A D
        (moduleKernelCellMap A D (moduleResolutionStage A D M n).hom))
      (moduleLocalizing_sphereCoproduct A D P hcop hperf _ _) ih

lemma moduleLocalizing_resolutionCandidate (M : ModuleCategory A D) :
    P ((moduleToDerived A D).obj (moduleResolutionCandidate A D M)) := by
  let F := moduleResolutionDiagram A D M
  let Q := sequentialCoproductFamily.{u} F
  have hp (j : ULift.{u} ℕ) : moduleHomotopicallyProjective A D (Q j) :=
    (moduleResolutionSemifreeFiltration A D M).stage_homotopicallyProjective A D (j.down + 1)
  have hQ : P ((moduleToDerived A D).obj (∐ Q)) :=
    moduleLocalizing_projectiveCoproduct A D P hcop Q hp
      (fun j => moduleLocalizing_resolutionStage A D P hcop hperf M j.down)
  have hcone : P ((moduleToDerived A D).obj
      (moduleCone A D (sequentialCoproductMap.{u} F))) :=
    P.ext_of_isTriangulatedClosed₃ _
      (moduleDerivedConeTriangle_distinguished A D (sequentialCoproductMap.{u} F)) hQ hQ
  exact P.prop_of_iso
    (moduleDerivedIso A D (moduleSequentialConeDesc A D F (colimit.cocone F))
      (moduleSequentialConeDesc_quasiIso A D F (colimit.cocone F) (colimit.isColimit F))) hcone

/-- perfect対象を含みu-small余積で閉じる三角部分圏は全主導来対象を含む。 -/
lemma moduleLocalizing_all (X : DerivedModuleCategory A D) : P X := by
  obtain ⟨⟨M⟩⟩ := X
  exact P.prop_of_iso
    (moduleDerivedIso A D (moduleResolutionCandidateπ A D M)
      (moduleResolutionCandidateπ_quasiIso A D M))
    (moduleLocalizing_resolutionCandidate A D P hcop hperf M)

end SerrePositivity.DifferentialGraded
end

end DerivedLocalizingGeneration
