module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.HomComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic
public import SerrePositivity.DifferentialGraded.Endomorphism.Module
public import SerrePositivity.DifferentialGraded.Derived.Projective

public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Functors


/-!
# Endomorphism.Derived.Adjunction

## 概要
射影性と Hom 同値による再構成 tensor–Hom 随伴をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## ActualScalarEnd（旧 SerrePositivity/DifferentialGraded/Endomorphism/ActualScalarEnd.lean） -/

/-! # 実際に係数変更した加群のEndとのdg比較 -/

@[expose] public section ActualScalarEnd
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D] (E : RightModule A D)

/-- 元のEndの係数変更から、実際の係数変更加群のEndへ向かう比較。 -/
def actualScalarEnd :
    DGFunctor A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
      (EndomorphismObject (ScalarExtension.rightModule φ D E)) where
  obj _ := .point
  map _ _ := scalarModuleHom φ D E E
  map_id _ := scalarModuleHom_identity φ D E
  map_comp _ _ _ := scalarModuleHom_composition φ D E E E

/-- 実際の加群圏へのEnd包含正方形。 -/
lemma actualScalarEnd_inclusion_square :
    (actualScalarEnd φ D E).comp
        (endomorphismInclusion A' (ScalarExtension.rightModule φ D E)) =
      (ScalarExtension.dgFunctor φ (endomorphismInclusion A E)).comp
        (scalarModuleDGFunctor φ D) := by
  apply EnrichedFunctor.ext (Complex A')
    (F := (actualScalarEnd φ D E).comp
      (endomorphismInclusion A' (ScalarExtension.rightModule φ D E)))
    (G := (ScalarExtension.dgFunctor φ (endomorphismInclusion A E)).comp
      (scalarModuleDGFunctor φ D)) (fun _ => rfl)
  intro x y
  simp only [DGFunctor.comp, EnrichedFunctor.comp_map, actualScalarEnd,
    endomorphismInclusion, scalarModuleDGFunctor, ScalarExtension.dgFunctor,
    CategoryTheory.Functor.map_id, Category.comp_id, eqToHom_refl]
  exact (Category.id_comp _).symm

/-- 評価も係数変更前の評価と既存の複体dg係数変更に接続する。 -/
lemma scalarModuleDGFunctor_evaluation_square (x : D) :
    (scalarModuleDGFunctor φ D).comp
        (moduleEvaluationDG A' (ScalarExtension.DGBaseChange φ D) x) =
      (ScalarExtension.dgFunctor φ (moduleEvaluationDG A D x)).comp
        (ScalarExtension.complexDGFunctor φ) := by
  apply EnrichedFunctor.ext (Complex A')
    (F := (scalarModuleDGFunctor φ D).comp
      (moduleEvaluationDG A' (ScalarExtension.DGBaseChange φ D) x))
    (G := (ScalarExtension.dgFunctor φ (moduleEvaluationDG A D x)).comp
      (ScalarExtension.complexDGFunctor φ)) (fun _ => rfl)
  intro M N
  simp only [DGFunctor.comp, EnrichedFunctor.comp_map, eqToHom_refl, Category.comp_id]
  exact scalarModuleHom_π φ D M N x

end SerrePositivity.DifferentialGraded
end

end ActualScalarEnd

/-! ## ActualScalarEvaluation（旧 SerrePositivity/DifferentialGraded/Endomorphism/ActualScalarEvaluation.lean） -/

/-! # 実際に係数変更したD上の加群のHomへ向かう導来評価図式 -/

@[expose] public section ActualScalarEvaluation
universe u v w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory BraidedCategory

lemma dgFunctor_endomorphismEvaluationComponent (A : Type u) [CommRing A]
    {C T : Type*} [DGCategory A C] [DGCategory A T]
    (F : DGFunctor A C T) (E X Y : C) :
    (F.map E Y ⊗ₘ F.map X E) ≫
        endomorphismEvaluationComponent A T (F.obj E) (F.obj X) (F.obj Y) =
      endomorphismEvaluationComponent A C E X Y ≫ F.map X Y := by
  unfold endomorphismEvaluationComponent
  change (F.map E Y ⊗ₘ F.map X E) ≫ (β_ _ _).hom ≫ _ = (β_ _ _).hom ≫ _ ≫ _
  rw [braiding_naturality_assoc, ← F.map_comp]

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D] (E X Y : RightModule A D)

def actualScalarEvaluation :
    BalancedTensor.obj A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
      (ScalarExtension.rightModule φ (EndomorphismObject E)
        (endomorphismHomRight A (RightModule A D) E Y))
      (ScalarExtension.leftModule φ (EndomorphismObject E)
        (endomorphismHomLeft A (RightModule A D) E X)) ⟶
      moduleHom A' (ScalarExtension.DGBaseChange φ D)
        (ScalarExtension.rightModule φ D X) (ScalarExtension.rightModule φ D Y) :=
  endomorphismScalarEvaluation φ (RightModule A D) E X Y ≫ scalarModuleHom φ D X Y

lemma actualScalarEvaluation_ι (b : EndomorphismObject E) :
    BalancedTensor.ι A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
        (ScalarExtension.rightModule φ (EndomorphismObject E)
          (endomorphismHomRight A (RightModule A D) E Y))
        (ScalarExtension.leftModule φ (EndomorphismObject E)
          (endomorphismHomLeft A (RightModule A D) E X)) b ≫
      actualScalarEvaluation φ D E X Y =
    (scalarModuleHom φ D E Y ⊗ₘ scalarModuleHom φ D X E) ≫
      endomorphismEvaluationComponent A' (RightModule A' (ScalarExtension.DGBaseChange φ D))
        (ScalarExtension.rightModule φ D E) (ScalarExtension.rightModule φ D X)
        (ScalarExtension.rightModule φ D Y) := by
  rw [actualScalarEvaluation, ← Category.assoc, endomorphismScalarEvaluation_ι]
  have h := dgFunctor_endomorphismEvaluationComponent A' (scalarModuleDGFunctor φ D) E X Y
  rw [endomorphismEvaluationComponentScalar]
  exact h.symm

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

lemma actualDerivedScalarEvaluation_square :
    ScalarExtension.derivedBalancedComparison φ (EndomorphismObject E)
        (endomorphismHomRight A (RightModule A D) E Y)
        (endomorphismHomLeft A (RightModule A D) E X) ≫
      DerivedCategory.Q.map (actualScalarEvaluation φ D E X Y) =
    (ScalarExtension.complexDerivedExtension φ).map
        (DerivedCategory.Q.map (endomorphismEvaluation A (RightModule A D) E X Y)) ≫
      (ScalarExtension.complexDerivedExtensionAugmentation φ).app (moduleHom A D X Y) ≫
        DerivedCategory.Q.map (scalarModuleHom φ D X Y) := by
  rw [actualScalarEvaluation, CategoryTheory.Functor.map_comp, ← Category.assoc,
    endomorphismDerivedScalarEvaluation_square, Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded
end

end ActualScalarEvaluation

/-! ## HomotopyAdjunction（旧 SerrePositivity/DifferentialGraded/Endomorphism/HomotopyAdjunction.lean） -/

/-! # 指定対象による再構成随伴の主ホモトピー圏への降下

dg関手が境界を保つことを使い、単位・余単位と三角恒等式を商へ送る。
-/

@[expose] public section HomotopyAdjunction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 再構成単位を主K(End(E))へ送る。 -/
def endomorphismHomotopyUnit :
    𝟭 (ModuleHomotopyCategory A (EndomorphismObject E)) ⟶
      (endomorphismModuleTensor A D E).onHomotopy ⋙
        (endomorphismModuleHom A D E).onHomotopy where
  app X := (moduleToHomotopy A (EndomorphismObject E)).map
    ((endomorphismModuleUnit A D E).app X.as)
  naturality {X Y} f := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨f, rfl⟩ := (moduleToHomotopy A (EndomorphismObject E)).map_surjective f
    change (moduleToHomotopy A (EndomorphismObject E)).map f ≫
        (moduleToHomotopy A (EndomorphismObject E)).map ((endomorphismModuleUnit A D E).app Y) =
      (moduleToHomotopy A (EndomorphismObject E)).map ((endomorphismModuleUnit A D E).app X) ≫
        (moduleToHomotopy A (EndomorphismObject E)).map
          ((endomorphismModuleHom A D E).onClosed.map
            ((endomorphismModuleTensor A D E).onClosed.map f))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (moduleToHomotopy A (EndomorphismObject E)).map
      ((endomorphismModuleUnit A D E).naturality f)

/-- 再構成余単位を主K(D)へ送る。 -/
def endomorphismHomotopyCounit :
    (endomorphismModuleHom A D E).onHomotopy ⋙
      (endomorphismModuleTensor A D E).onHomotopy ⟶ 𝟭 (ModuleHomotopyCategory A D) where
  app X := (moduleToHomotopy A D).map ((endomorphismModuleCounit A D E).app X.as)
  naturality {X Y} f := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨f, rfl⟩ := (moduleToHomotopy A D).map_surjective f
    change (moduleToHomotopy A D).map
        ((endomorphismModuleTensor A D E).onClosed.map
          ((endomorphismModuleHom A D E).onClosed.map f)) ≫
        (moduleToHomotopy A D).map ((endomorphismModuleCounit A D E).app Y) =
      (moduleToHomotopy A D).map ((endomorphismModuleCounit A D E).app X) ≫
        (moduleToHomotopy A D).map f
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (moduleToHomotopy A D).map ((endomorphismModuleCounit A D E).naturality f)

lemma endomorphismHomotopy_left_triangle (X : ModuleHomotopyCategory A (EndomorphismObject E)) :
    (endomorphismModuleTensor A D E).onHomotopy.map ((endomorphismHomotopyUnit A D E).app X) ≫
      (endomorphismHomotopyCounit A D E).app
        ((endomorphismModuleTensor A D E).onHomotopy.obj X) = 𝟙 _ := by
  obtain ⟨X⟩ := X
  change (moduleToHomotopy A D).map
      ((endomorphismModuleTensor A D E).onClosed.map ((endomorphismModuleUnit A D E).app X)) ≫
    (moduleToHomotopy A D).map ((endomorphismModuleCounit A D E).app
      ((endomorphismModuleTensor A D E).onClosed.obj X)) = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp, endomorphismModule_left_triangle,
    CategoryTheory.Functor.map_id]

lemma endomorphismHomotopy_right_triangle (X : ModuleHomotopyCategory A D) :
    (endomorphismHomotopyUnit A D E).app ((endomorphismModuleHom A D E).onHomotopy.obj X) ≫
      (endomorphismModuleHom A D E).onHomotopy.map
        ((endomorphismHomotopyCounit A D E).app X) = 𝟙 _ := by
  obtain ⟨X⟩ := X
  change (moduleToHomotopy A (EndomorphismObject E)).map
      ((endomorphismModuleUnit A D E).app ((endomorphismModuleHom A D E).onClosed.obj X)) ≫
    (moduleToHomotopy A (EndomorphismObject E)).map
      ((endomorphismModuleHom A D E).onClosed.map ((endomorphismModuleCounit A D E).app X)) = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp, endomorphismModule_right_triangle,
    CategoryTheory.Functor.map_id]

/-- 主ホモトピー圏間の再構成tensor–Hom随伴。 -/
def endomorphismHomotopyAdjunction :
    (endomorphismModuleTensor A D E).onHomotopy ⊣ (endomorphismModuleHom A D E).onHomotopy :=
  Adjunction.mkOfUnitCounit
    { unit := endomorphismHomotopyUnit A D E
      counit := endomorphismHomotopyCounit A D E
      left_triangle := by
        apply NatTrans.ext
        funext X
        simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_hom_app, Category.id_comp, Category.comp_id,
          Functor.comp_obj, Functor.id_obj, NatTrans.id] using
            endomorphismHomotopy_left_triangle A D E X
      right_triangle := by
        apply NatTrans.ext
        funext X
        simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_inv_app, Category.id_comp, Category.comp_id,
          Functor.comp_obj, Functor.id_obj, NatTrans.id] using
            endomorphismHomotopy_right_triangle A D E X }

end SerrePositivity.DifferentialGraded
end

end HomotopyAdjunction

/-! ## ProjectiveCriterion（旧 SerrePositivity/DifferentialGraded/Endomorphism/ProjectiveCriterion.lean） -/

/-! # 主KにおけるHom計算によるホモトピー射影性の判定

指定射影解像度のK内retractを使う。新たな生成定理や引用を仮定しない。
-/

@[expose] public section ProjectiveCriterion
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- K内で射影的加群のretractになる実際のdg加群もホモトピー射影的。 -/
lemma moduleHomotopicallyProjective_of_homotopyRetract
    {P Q : ModuleCategory A D} (i : P ⟶ Q) (r : Q ⟶ P)
    (h : (moduleToHomotopy A D).map (i ≫ r) = (moduleToHomotopy A D).map (𝟙 P))
    (hQ : moduleHomotopicallyProjective A D Q) : moduleHomotopicallyProjective A D P := by
  intro T hT q
  apply (exactAt_iff_isZero_homology _ q).2
  have hz := (hQ T hT q).isZero_homology
  obtain ⟨hh⟩ := (moduleToHomotopy_map_eq_iff A D (i ≫ r) (𝟙 P)).mp h
  have he := (moduleHomPrecomposeHomotopy A D hh T).homologyMap_eq q
  simp only [eHomWhiskerRight_comp, eHomWhiskerRight_id, homologyMap_comp, homologyMap_id] at he
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 (homology (P ⟶[Complex A] T) q) = 0
  change IsZero (homology (Q ⟶[Complex A] T) q) at hz
  rw [← he, hz.eq_of_tgt (homologyMap (eHomWhiskerRight (Complex A) r T) q) 0, zero_comp]

/-- KのHom(P,−)が指定擬同型を反転すれば、指定解像度がK内で分裂しPは射影的。 -/
lemma moduleHomotopicallyProjective_of_coyoneda_inverts (P : ModuleCategory A D)
    (hP : (moduleHomotopyQuasiIso A D).IsInvertedBy
      (coyoneda.obj (op ((moduleToHomotopy A D).obj P)))) :
    moduleHomotopicallyProjective A D P := by
  let R := moduleCanonicalProjectiveResolution A D P
  have hW := (moduleHomotopyQuasiIso_map_iff A D R.π).mpr R.quasiIso
  have hi := hP ((moduleToHomotopy A D).map R.π) hW
  have hb := (CategoryTheory.isIso_iff_bijective _).mp hi
  obtain ⟨s, hs⟩ := hb.2 (𝟙 ((moduleToHomotopy A D).obj P))
  obtain ⟨i, hi⟩ := (moduleToHomotopy A D).map_surjective s
  apply moduleHomotopicallyProjective_of_homotopyRetract A D i R.π _ R.projective
  rw [CategoryTheory.Functor.map_comp, hi, CategoryTheory.Functor.map_id]
  exact hs

/-- 主K上のcoyonedaによるホモトピー射影性の同値な判定。 -/
lemma moduleHomotopicallyProjective_iff_coyoneda_inverts (P : ModuleCategory A D) :
    moduleHomotopicallyProjective A D P ↔
      (moduleHomotopyQuasiIso A D).IsInvertedBy
        (coyoneda.obj (op ((moduleToHomotopy A D).obj P))) :=
  ⟨moduleHomotopicallyProjective_coyoneda_inverts A D,
    moduleHomotopicallyProjective_of_coyoneda_inverts A D P⟩

end SerrePositivity.DifferentialGraded
end

end ProjectiveCriterion

/-! ## TensorProjective（旧 SerrePositivity/DifferentialGraded/Endomorphism/TensorProjective.lean） -/

/-! # 指定射影的dg加群とのtensorによるホモトピー射影性の保存

主K上の随伴とHomの擬同型保存から、coyonedaによる判定を用いる。
-/

@[expose] public section TensorProjective
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- Eの射影性の下で、主K上のHom関手も指定擬同型を保つ。 -/
lemma endomorphismHomotopyHom_quasiIso
    (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))
    {M N : ModuleHomotopyCategory A D} (f : M ⟶ N) (hf : moduleHomotopyQuasiIso A D f) :
    moduleHomotopyQuasiIso A (EndomorphismObject E)
      ((endomorphismModuleHom A D E).onHomotopy.map f) := by
  obtain ⟨M⟩ := M
  obtain ⟨N⟩ := N
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  change moduleHomotopyQuasiIso A (EndomorphismObject E)
    ((moduleToHomotopy A (EndomorphismObject E)).map
      ((endomorphismModuleHom A D E).onClosed.map g))
  exact (moduleHomotopyQuasiIso_map_iff A (EndomorphismObject E) _).mpr
    (endomorphismModuleHom_quasiIso A D E hE g ((moduleHomotopyQuasiIso_map_iff A D g).mp hf))

/-- Eがホモトピー射影的なら、再構成tensorは射影的右End(E)加群を射影的右D加群へ送る。 -/
lemma endomorphismModuleTensor_homotopicallyProjective
    (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))
    {P : ModuleCategory A (EndomorphismObject E)}
    (hP : moduleHomotopicallyProjective A (EndomorphismObject E) P) :
    moduleHomotopicallyProjective A D ((endomorphismModuleTensor A D E).onClosed.obj P) := by
  apply moduleHomotopicallyProjective_of_coyoneda_inverts A D
  intro X Y f hf
  apply (CategoryTheory.isIso_iff_bijective _).mpr
  let adj := endomorphismHomotopyAdjunction A D E
  let Rf := (endomorphismModuleHom A D E).onHomotopy.map f
  have hRf := endomorphismHomotopyHom_quasiIso A D E hE f hf
  have hpost := (CategoryTheory.isIso_iff_bijective _).mp
    (moduleHomotopicallyProjective_coyoneda_inverts A (EndomorphismObject E) hP Rf hRf)
  change Function.Bijective (fun s :
      (endomorphismModuleTensor A D E).onHomotopy.obj
        ((moduleToHomotopy A (EndomorphismObject E)).obj P) ⟶ X => s ≫ f)
  let eX := adj.homEquiv ((moduleToHomotopy A (EndomorphismObject E)).obj P) X
  let eY := adj.homEquiv ((moduleToHomotopy A (EndomorphismObject E)).obj P) Y
  have heq : (fun s :
      (endomorphismModuleTensor A D E).onHomotopy.obj
        ((moduleToHomotopy A (EndomorphismObject E)).obj P) ⟶ X => s ≫ f) =
      fun s => eY.symm (eX s ≫ Rf) := by
    funext s
    apply eY.injective
    rw [Equiv.apply_symm_apply]
    exact adj.homEquiv_naturality_right s f
  rw [heq]
  exact eY.symm.bijective.comp (hpost.comp eX.bijective)

end SerrePositivity.DifferentialGraded
end

end TensorProjective

/-! ## DerivedHomEquiv（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedHomEquiv.lean） -/

/-! # 再構成導来tensorと導来Homの射集合の比較

射影解像度、主Kの随伴、射影的始域の局所化Hom計算を組み合わせる。
ここでの射集合同値の両変数自然性は、導来随伴を組み立てる際の別証明義務。
-/

@[expose] public section DerivedHomEquiv
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

/-- 実際の加群の主導来像における導来Homの計算。 -/
def endomorphismDerivedHomComputation (M : ModuleCategory A D) :
    (endomorphismDerivedHom A D E hE).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A (EndomorphismObject E)).obj
        ((endomorphismModuleHom A D E).onClosed.obj M) :=
  eqToIso (congrArg (fun F => F.obj M) (endomorphismDerivedHom_fac A D E hE))

/-- 射影的右End(E)加群を始域とする、導来圏のHomの実際の同値。 -/
def endomorphismProjectiveDerivedHomEquiv
    (P : ModuleCategory A (EndomorphismObject E))
    (hP : moduleHomotopicallyProjective A (EndomorphismObject E) P) (M : ModuleCategory A D) :
    ((moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj P) ⟶
        (moduleToDerived A D).obj M) ≃
      ((moduleToDerived A (EndomorphismObject E)).obj P ⟶
        (endomorphismDerivedHom A D E hE).obj ((moduleToDerived A D).obj M)) :=
  (moduleProjectiveDerivedHomEquiv A D
      (endomorphismModuleTensor_homotopicallyProjective A D E hE hP) M).symm.trans
    (((endomorphismHomotopyAdjunction A D E).homEquiv
      ((moduleToHomotopy A (EndomorphismObject E)).obj P) ((moduleToHomotopy A D).obj M)).trans
      ((moduleProjectiveDerivedHomEquiv A (EndomorphismObject E) hP
        ((endomorphismModuleHom A D E).onClosed.obj M)).trans
          (Iso.homCongr (Iso.refl _) (endomorphismDerivedHomComputation A D E hE M).symm)))

/-- 任意の右End(E)加群と右D加群の主導来像におけるtensor–Hom同値。 -/
def endomorphismDerivedTensorHomEquivOnModules
    (N : ModuleCategory A (EndomorphismObject E)) (M : ModuleCategory A D) :
    ((endomorphismDerivedTensor A D E).obj ((moduleToDerived A (EndomorphismObject E)).obj N) ⟶
        (moduleToDerived A D).obj M) ≃
      ((moduleToDerived A (EndomorphismObject E)).obj N ⟶
        (endomorphismDerivedHom A D E hE).obj ((moduleToDerived A D).obj M)) := by
  let P := moduleCanonicalProjectiveResolution A (EndomorphismObject E) N
  exact (Iso.homCongr (endomorphismDerivedTensorResolutionComputation A D E P) (Iso.refl _)).trans
    ((endomorphismProjectiveDerivedHomEquiv A D E hE P.obj P.projective M).trans
      (Iso.homCongr (moduleDerivedIso A (EndomorphismObject E) P.π P.quasiIso) (Iso.refl _)))

/-- 主導来圏の任意の対象についてのtensor–Hom射集合同値。 -/
def endomorphismDerivedTensorHomEquiv
    (X : DerivedModuleCategory A (EndomorphismObject E)) (Y : DerivedModuleCategory A D) :
    ((endomorphismDerivedTensor A D E).obj X ⟶ Y) ≃
      (X ⟶ (endomorphismDerivedHom A D E hE).obj Y) :=
  endomorphismDerivedTensorHomEquivOnModules A D E hE X.as.obj Y.as.obj

end SerrePositivity.DifferentialGraded
end

end DerivedHomEquiv

/-! ## DerivedProjectiveHomNaturality（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedProjectiveHomNaturality.lean） -/

/-! # 射影的始域での再構成Hom同値の自然性 -/

@[expose] public section DerivedProjectiveHomNaturality
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

lemma endomorphismHomotopyHomEquiv_map
    (P : ModuleCategory A (EndomorphismObject E)) (M : ModuleCategory A D)
    (s : (endomorphismModuleTensor A D E).onClosed.obj P ⟶ M) :
    (endomorphismHomotopyAdjunction A D E).homEquiv
        ((moduleToHomotopy A (EndomorphismObject E)).obj P) ((moduleToHomotopy A D).obj M)
        ((moduleToHomotopy A D).map s) =
      (moduleToHomotopy A (EndomorphismObject E)).map
        ((endomorphismModuleAdjunction A D E).homEquiv P M s) := by
  rw [Adjunction.homEquiv_unit]
  change (moduleToHomotopy A (EndomorphismObject E)).map
      ((endomorphismModuleUnit A D E).app P) ≫
    (moduleToHomotopy A (EndomorphismObject E)).map
      ((endomorphismModuleHom A D E).onClosed.map s) = _
  rw [← Functor.map_comp]
  exact congrArg (moduleToHomotopy A (EndomorphismObject E)).map
    ((endomorphismModuleAdjunction A D E).homEquiv_unit P M s).symm

variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

lemma endomorphismProjectiveDerivedHomEquiv_map
    (P : ModuleCategory A (EndomorphismObject E))
    (hP : moduleHomotopicallyProjective A (EndomorphismObject E) P)
    (M : ModuleCategory A D)
    (s : (endomorphismModuleTensor A D E).onClosed.obj P ⟶ M) :
    endomorphismProjectiveDerivedHomEquiv A D E hE P hP M ((moduleToDerived A D).map s) =
      (moduleToDerived A (EndomorphismObject E)).map
          ((endomorphismModuleAdjunction A D E).homEquiv P M s) ≫
        (endomorphismDerivedHomComputation A D E hE M).inv := by
  have hs := moduleProjectiveDerivedHomEquiv_map A D
    (endomorphismModuleTensor_homotopicallyProjective A D E hE hP) s
  unfold endomorphismProjectiveDerivedHomEquiv
  simp only [Equiv.trans_apply]
  rw [← hs, Equiv.symm_apply_apply]
  have ht := endomorphismHomotopyHomEquiv_map A D E P M s
  have hu := congrArg
    (moduleProjectiveDerivedHomEquiv A (EndomorphismObject E) hP
      ((endomorphismModuleHom A D E).onClosed.obj M)) ht
  have hv := hu.trans (moduleProjectiveDerivedHomEquiv_map A (EndomorphismObject E) hP
    ((endomorphismModuleAdjunction A D E).homEquiv P M s))
  exact (congrArg
    (Iso.homCongr (Iso.refl _) (endomorphismDerivedHomComputation A D E hE M).symm) hv).trans
      (by simp [Iso.homCongr])

lemma endomorphismDerivedHomComputation_inv_naturality
    {M M' : ModuleCategory A D} (f : M ⟶ M') :
    (moduleToDerived A (EndomorphismObject E)).map
        ((endomorphismModuleHom A D E).onClosed.map f) ≫
        (endomorphismDerivedHomComputation A D E hE M').inv =
      (endomorphismDerivedHomComputation A D E hE M).inv ≫
        (endomorphismDerivedHom A D E hE).map ((moduleToDerived A D).map f) := by
  exact (eqToIso (endomorphismDerivedHom_fac A D E hE)).inv.naturality f

lemma endomorphismProjectiveDerivedHomEquiv_naturality_right
    (P : ModuleCategory A (EndomorphismObject E))
    (hP : moduleHomotopicallyProjective A (EndomorphismObject E) P)
    {M M' : ModuleCategory A D}
    (φ : (moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj P) ⟶
      (moduleToDerived A D).obj M) (f : M ⟶ M') :
    endomorphismProjectiveDerivedHomEquiv A D E hE P hP M'
        (φ ≫ (moduleToDerived A D).map f) =
      endomorphismProjectiveDerivedHomEquiv A D E hE P hP M φ ≫
        (endomorphismDerivedHom A D E hE).map ((moduleToDerived A D).map f) := by
  obtain ⟨s, rfl⟩ := moduleProjectiveToDerived_map_surjective A D
    (endomorphismModuleTensor_homotopicallyProjective A D E hE hP) φ
  rw [← Functor.map_comp, endomorphismProjectiveDerivedHomEquiv_map,
    endomorphismProjectiveDerivedHomEquiv_map,
    Adjunction.homEquiv_naturality_right, Functor.map_comp, Category.assoc,
    endomorphismDerivedHomComputation_inv_naturality, Category.assoc]

lemma endomorphismProjectiveDerivedHomEquiv_naturality_left
    (P Q : ModuleCategory A (EndomorphismObject E))
    (hP : moduleHomotopicallyProjective A (EndomorphismObject E) P)
    (hQ : moduleHomotopicallyProjective A (EndomorphismObject E) Q)
    (M : ModuleCategory A D) (f : P ⟶ Q)
    (φ : (moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj Q) ⟶
      (moduleToDerived A D).obj M) :
    endomorphismProjectiveDerivedHomEquiv A D E hE P hP M
        ((moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map f) ≫ φ) =
      (moduleToDerived A (EndomorphismObject E)).map f ≫
        endomorphismProjectiveDerivedHomEquiv A D E hE Q hQ M φ := by
  obtain ⟨s, rfl⟩ := moduleProjectiveToDerived_map_surjective A D
    (endomorphismModuleTensor_homotopicallyProjective A D E hE hQ) φ
  rw [← Functor.map_comp, endomorphismProjectiveDerivedHomEquiv_map,
    endomorphismProjectiveDerivedHomEquiv_map,
    Adjunction.homEquiv_naturality_left, Functor.map_comp, Category.assoc]

end SerrePositivity.DifferentialGraded
end

end DerivedProjectiveHomNaturality

/-! ## DerivedHomNaturality（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedHomNaturality.lean） -/

/-! # 再構成導来Hom同値の実際の加群射に対する自然性 -/

@[expose] public section DerivedHomNaturality
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

lemma endomorphismDerivedTensorHomEquivOnModules_apply
    (N : ModuleCategory A (EndomorphismObject E)) (M : ModuleCategory A D)
    (φ : (endomorphismDerivedTensor A D E).obj
        ((moduleToDerived A (EndomorphismObject E)).obj N) ⟶ (moduleToDerived A D).obj M) :
    endomorphismDerivedTensorHomEquivOnModules A D E hE N M φ =
      (moduleDerivedIso A (EndomorphismObject E)
          (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N).π
          (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N).quasiIso).inv ≫
        endomorphismProjectiveDerivedHomEquiv A D E hE
          (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N).obj
          (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N).projective M
          ((endomorphismDerivedTensorResolutionComputation A D E
            (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N)).inv ≫ φ) := by
  simp [endomorphismDerivedTensorHomEquivOnModules, Iso.homCongr]

lemma endomorphismDerivedTensorHomEquivOnModules_naturality_right
    (N : ModuleCategory A (EndomorphismObject E)) {M M' : ModuleCategory A D}
    (φ : (endomorphismDerivedTensor A D E).obj
        ((moduleToDerived A (EndomorphismObject E)).obj N) ⟶ (moduleToDerived A D).obj M)
    (f : M ⟶ M') :
    endomorphismDerivedTensorHomEquivOnModules A D E hE N M'
        (φ ≫ (moduleToDerived A D).map f) =
      endomorphismDerivedTensorHomEquivOnModules A D E hE N M φ ≫
        (endomorphismDerivedHom A D E hE).map ((moduleToDerived A D).map f) := by
  rw [endomorphismDerivedTensorHomEquivOnModules_apply,
    endomorphismDerivedTensorHomEquivOnModules_apply, ← Category.assoc,
    endomorphismProjectiveDerivedHomEquiv_naturality_right, Category.assoc]

lemma endomorphismResolutionLift_derived_fac
    {N N' : ModuleCategory A (EndomorphismObject E)}
    (P : ModuleProjectiveResolution A (EndomorphismObject E) N)
    (Q : ModuleProjectiveResolution A (EndomorphismObject E) N') (f : N ⟶ N') :
    (moduleToDerived A (EndomorphismObject E)).map (P.lift Q f) ≫
        (moduleToDerived A (EndomorphismObject E)).map Q.π =
      (moduleToDerived A (EndomorphismObject E)).map P.π ≫
        (moduleToDerived A (EndomorphismObject E)).map f := by
  have h := P.lift_fac Q f
  rw [← Functor.map_comp, ← Functor.map_comp] at h
  have h' := moduleQuasiIso_equalizes_boundary A (EndomorphismObject E)
    (moduleToDerived A (EndomorphismObject E))
    (moduleToDerived_inverts A (EndomorphismObject E)) _ _
    ((toHomotopy_map_eq_iff A (RightModule A (EndomorphismObject E)) _ _).mp h)
  simpa only [Functor.map_comp] using h'

lemma endomorphismResolutionLift_derived_inv_naturality
    {N N' : ModuleCategory A (EndomorphismObject E)}
    (P : ModuleProjectiveResolution A (EndomorphismObject E) N)
    (Q : ModuleProjectiveResolution A (EndomorphismObject E) N') (f : N ⟶ N') :
    (moduleDerivedIso A (EndomorphismObject E) P.π P.quasiIso).inv ≫
        (moduleToDerived A (EndomorphismObject E)).map (P.lift Q f) =
      (moduleToDerived A (EndomorphismObject E)).map f ≫
        (moduleDerivedIso A (EndomorphismObject E) Q.π Q.quasiIso).inv := by
  apply (cancel_mono (moduleDerivedIso A (EndomorphismObject E) Q.π Q.quasiIso).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (moduleDerivedIso A (EndomorphismObject E) P.π P.quasiIso).inv ≫
    (moduleToDerived A (EndomorphismObject E)).map (P.lift Q f) ≫
      (moduleToDerived A (EndomorphismObject E)).map Q.π = _
  rw [endomorphismResolutionLift_derived_fac]
  exact Iso.inv_hom_id_assoc _ _

lemma endomorphismDerivedTensorHomEquivOnModules_naturality_left
    {N N' : ModuleCategory A (EndomorphismObject E)} (M : ModuleCategory A D)
    (f : N ⟶ N')
    (φ : (endomorphismDerivedTensor A D E).obj
        ((moduleToDerived A (EndomorphismObject E)).obj N') ⟶ (moduleToDerived A D).obj M) :
    endomorphismDerivedTensorHomEquivOnModules A D E hE N M
        ((endomorphismDerivedTensor A D E).map
          ((moduleToDerived A (EndomorphismObject E)).map f) ≫ φ) =
      (moduleToDerived A (EndomorphismObject E)).map f ≫
        endomorphismDerivedTensorHomEquivOnModules A D E hE N' M φ := by
  rw [endomorphismDerivedTensorHomEquivOnModules_apply,
    endomorphismDerivedTensorHomEquivOnModules_apply, ← Category.assoc,
    endomorphismDerivedTensorResolutionComputation_inv_naturality, Category.assoc,
    endomorphismProjectiveDerivedHomEquiv_naturality_left, ← Category.assoc,
    endomorphismResolutionLift_derived_inv_naturality, Category.assoc]

end SerrePositivity.DifferentialGraded
end

end DerivedHomNaturality

/-! ## DerivedAdjunction（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedAdjunction.lean） -/

/-! # 指定ホモトピー射影的加群による主導来tensor–Hom随伴

解像度で構成した射集合同値の自然性を局所化の全射へ拡張する。
compact生成性やMorita同値はここでは仮定せず、結論も随伴まで。
-/

@[expose] public section DerivedAdjunction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

lemma endomorphismDerivedTensorHomEquiv_naturality_right
    (X : DerivedModuleCategory A (EndomorphismObject E))
    {Y Y' : DerivedModuleCategory A D}
    (φ : (endomorphismDerivedTensor A D E).obj X ⟶ Y) (g : Y ⟶ Y') :
    endomorphismDerivedTensorHomEquiv A D E hE X Y' (φ ≫ g) =
      endomorphismDerivedTensorHomEquiv A D E hE X Y φ ≫
        (endomorphismDerivedHom A D E hE).map g := by
  apply localizationHom_naturality_right (moduleQuasiIso A D)
    (endomorphismDerivedTensor A D E) (endomorphismDerivedHom A D E hE)
    (fun X Y φ => endomorphismDerivedTensorHomEquiv A D E hE X Y φ)
  intro X M M' f φ
  exact endomorphismDerivedTensorHomEquivOnModules_naturality_right A D E hE X.as.obj φ f

lemma endomorphismDerivedTensorHomEquiv_naturality_left
    {X X' : DerivedModuleCategory A (EndomorphismObject E)}
    (f : X ⟶ X') (Y : DerivedModuleCategory A D)
    (φ : (endomorphismDerivedTensor A D E).obj X' ⟶ Y) :
    endomorphismDerivedTensorHomEquiv A D E hE X Y
        ((endomorphismDerivedTensor A D E).map f ≫ φ) =
      f ≫ endomorphismDerivedTensorHomEquiv A D E hE X' Y φ := by
  apply localizationHom_naturality_left (moduleQuasiIso A (EndomorphismObject E))
    (endomorphismDerivedTensor A D E) (endomorphismDerivedHom A D E hE)
    (fun X Y φ => endomorphismDerivedTensorHomEquiv A D E hE X Y φ)
  intro N N' f Y φ
  exact endomorphismDerivedTensorHomEquivOnModules_naturality_left A D E hE Y.as.obj f φ

/-- 射影解像度による再構成導来tensorと導来Homの実際の随伴。 -/
def endomorphismDerivedAdjunction :
    endomorphismDerivedTensor A D E ⊣ endomorphismDerivedHom A D E hE :=
  Adjunction.mkOfHomEquiv
    { homEquiv := endomorphismDerivedTensorHomEquiv A D E hE
      homEquiv_naturality_right := fun φ g =>
        endomorphismDerivedTensorHomEquiv_naturality_right A D E hE _ φ g
      homEquiv_naturality_left_symm := by
        intro X X' Y f g
        apply (endomorphismDerivedTensorHomEquiv A D E hE X Y).injective
        rw [Equiv.apply_symm_apply, endomorphismDerivedTensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply] }

/-- 主導来再構成随伴の単位。 -/
def endomorphismDerivedUnit :
    𝟭 (DerivedModuleCategory A (EndomorphismObject E)) ⟶
      endomorphismDerivedTensor A D E ⋙ endomorphismDerivedHom A D E hE :=
  (endomorphismDerivedAdjunction A D E hE).unit

/-- 主導来再構成随伴の余単位。 -/
def endomorphismDerivedCounit :
    endomorphismDerivedHom A D E hE ⋙ endomorphismDerivedTensor A D E ⟶
      𝟭 (DerivedModuleCategory A D) :=
  (endomorphismDerivedAdjunction A D E hE).counit

lemma endomorphismDerived_left_triangle (X : DerivedModuleCategory A (EndomorphismObject E)) :
    (endomorphismDerivedTensor A D E).map ((endomorphismDerivedUnit A D E hE).app X) ≫
      (endomorphismDerivedCounit A D E hE).app ((endomorphismDerivedTensor A D E).obj X) = 𝟙 _ :=
  (endomorphismDerivedAdjunction A D E hE).left_triangle_components X

lemma endomorphismDerived_right_triangle (Y : DerivedModuleCategory A D) :
    (endomorphismDerivedUnit A D E hE).app ((endomorphismDerivedHom A D E hE).obj Y) ≫
      (endomorphismDerivedHom A D E hE).map ((endomorphismDerivedCounit A D E hE).app Y) = 𝟙 _ :=
  (endomorphismDerivedAdjunction A D E hE).right_triangle_components Y

end SerrePositivity.DifferentialGraded
end

end DerivedAdjunction

/-! ## DerivedGenerators（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedGenerators.lean） -/

/-! # 再構成導来随伴による指定対象と正則End加群の比較

正則End加群の射影性で導来tensorを直接計算し、既存のYoneda tensor単位に接続する。
-/

@[expose] public section DerivedGenerators
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 射影的加群について、再構成導来tensorは非導来tensorで計算できる。 -/
def endomorphismDerivedTensorProjectiveComputation
    (N : ModuleCategory A (EndomorphismObject E))
    (hN : moduleHomotopicallyProjective A (EndomorphismObject E) N) :
    (endomorphismDerivedTensor A D E).obj
        ((moduleToDerived A (EndomorphismObject E)).obj N) ≅
      (moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj N) :=
  endomorphismDerivedTensorResolutionComputation A D E
    { obj := N
      π := 𝟙 N
      projective := hN
      quasiIso := (moduleQuasiIso A (EndomorphismObject E)).id_mem N }

/-- 正則End(E)加群は再構成導来tensorで指定対象Eに送られる。 -/
def endomorphismDerivedTensor_regularIso :
    (endomorphismDerivedTensor A D E).obj
        ((moduleToDerived A (EndomorphismObject E)).obj
          (ForgetEnrichment.of (Complex A) (representable A (EndomorphismObject.point (E := E))))) ≅
      (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) E) :=
  endomorphismDerivedTensorProjectiveComputation A D E _
      (representable_homotopicallyProjective A (EndomorphismObject E) .point) ≪≫
    (moduleToDerived A D).mapIso (endomorphismModuleTensor_regularIso A D E)

/-- 指定対象Eの導来Hom像は正則End(E)加群。 -/
def endomorphismDerivedHom_selfIso
    (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E)) :
    (endomorphismDerivedHom A D E hE).obj
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) E)) ≅
      (moduleToDerived A (EndomorphismObject E)).obj
        (ForgetEnrichment.of (Complex A) (representable A (EndomorphismObject.point (E := E)))) :=
  endomorphismDerivedHomComputation A D E hE (ForgetEnrichment.of (Complex A) E) ≪≫
    (moduleToDerived A (EndomorphismObject E)).mapIso
      (eqToIso (congrArg (ForgetEnrichment.of (Complex A)) (endomorphismModuleHom_self A D E)))

end SerrePositivity.DifferentialGraded
end

end DerivedGenerators

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.8.5.8" (partial := stronger-hyp) "仮定：小さい dg 圏 D、その指定範囲の完全 dg 加群 E、E の thick 生成と全導来圏での compact generator 性（Lean が強い：通常の dg 導来圏に限り、これらの生成仮定を追加する）。結論：End(E) 上の加群の通常の導来圏から D 上の導来圏への同値を構成し、正則 End(E) 加群を E と同定する（この仮定での HA の結論の一部に一致）。一般の C-線型 ∞ 圏での六条件の同値は含まれない。"] _root_.SerrePositivity.DifferentialGraded.endomorphismDerivedTensor_regularIso
attribute [cite HA "7.1.2.3" (partial := stronger-hyp) "仮定：小さい dg 圏と指定した完全 compact generator E、追加の thick 生成（Lean が強い：通常の dg 導来圏の場合）。結論：表示に用いる代数を End(E) と明示し、正則加群の像を E と同定する（この仮定での HA の結論の一部に一致）。環スペクトルの自己準同型代数との比較は含まれない。"] _root_.SerrePositivity.DifferentialGraded.endomorphismDerivedTensor_regularIso
