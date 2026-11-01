module

public import SerrePositivity.DifferentialGraded.Bimodule.Tensor
public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import Mathlib.CategoryTheory.Equivalence
public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import SerrePositivity.DifferentialGraded.Module.Isomorphism
public import SerrePositivity.DifferentialGraded.Module.RestrictionColimits
public import SerrePositivity.DifferentialGraded.Module.Semifree.Resolution
public import SerrePositivity.DifferentialGraded.Category.TensorComposition
public import SerrePositivity.DifferentialGraded.Module.RestrictionAction
public import SerrePositivity.DifferentialGraded.Module.Free
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation
public import SerrePositivity.DifferentialGraded.Module.RestrictionTensor
public import SerrePositivity.DifferentialGraded.Tensor.Fubini
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon

/-!
# Bimodule.Right

## 概要
17 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## UncurryNaturality（旧 SerrePositivity/DifferentialGraded/Bimodule/UncurryNaturality.lean） -/

/-! # 閉零bimodule射の積dg圏上の全Hom自然性

## 概要
閉零bimodule射の積dg圏上の全Hom自然性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/TensorModuleFull.lean。局所導来合成の計算部品、一般Morita・
相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section UncurryNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 右作用と左作用に自然な閉零射は、積の全Homにも自然である。 -/
lemma valueMap_uncurry_naturality {M N : BimoduleCategory A B C} (a : M ⟶ N)
    (x y : DGTensorCategory A Bᵒᵖ C) :
    (underlying A B C M).uncurryHom x y ≫
      homPostcompose ((underlying A B C M).value x.1.unop x.2)
        ((valueEvaluation A B C y.1.unop y.2).map a) =
    (underlying A B C N).uncurryHom x y ≫
      homPrecompose ((valueEvaluation A B C x.1.unop x.2).map a)
        ((underlying A B C N).value y.1.unop y.2) := by
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change (homPostcompose _ _).f n
    (((underlying A B C M).uncurryHom x y).f n (dgTensorElement A f g hn)) =
    (homPrecompose _ _).f n
      (((underlying A B C N).uncurryHom x y).f n (dgTensorElement A f g hn))
  rw [Bimodule.uncurryHom_apply, Bimodule.uncurryHom_apply]
  simp only [Units.smul_def, map_zsmul]
  apply congrArg (((p * q).negOnePow : ℤ) • ·)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply Cochain.ext
  intro i j hij
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply,
    Cochain.comp_v _ _ hn i (i + p) j rfl (by omega),
    Cochain.comp_v _ _ hn i (i + p) j rfl (by omega)]
  change ((valueEvaluation A B C y.1.unop y.2).map a).f j
    (leftAction A ((underlying A B C M).leftAt y.1.unop) g
      (moduleAction A ((underlying A B C M).rightAt x.2) f z rfl) (by omega)) =
    leftAction A ((underlying A B C N).leftAt y.1.unop) g
      (moduleAction A ((underlying A B C N).rightAt x.2) f
        (((valueEvaluation A B C x.1.unop x.2).map a).f i z) rfl) (by omega)
  rw [valueMap_leftAction, valueMap_rightAction]

end SerrePositivity.DifferentialGraded.BimoduleCategory
end

end UncurryNaturality

/-! ## TensorModuleFull（旧 SerrePositivity/DifferentialGraded/Bimodule/TensorModuleFull.lean） -/

/-! # 積dg圏上の加群とbimoduleの閉零圏の同値

## 概要
積dg圏上の加群とbimoduleの閉零圏の同値。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/RightModuleComparison.lean。局所導来合成の計算部品、
一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section TensorModuleFull
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensorModule
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma preimage_naturality {M N : BimoduleTensorModuleCategory A B C}
    (a : (functor A B C).obj M ⟶ (functor A B C).obj N)
    (x y : DGTensorCategory A Bᵒᵖ C) :
    (underlying A B C M).map x y ≫
      homPostcompose ((underlying A B C M).obj x)
        ((BimoduleCategory.valueEvaluation A B C y.1.unop y.2).map a) =
    (underlying A B C N).map x y ≫
      homPrecompose ((BimoduleCategory.valueEvaluation A B C x.1.unop x.2).map a)
        ((underlying A B C N).obj y) := by
  have h := BimoduleCategory.valueMap_uncurry_naturality A B C a x y
  change (underlying A B C M).toBimodule.toTensorFunctor.map x y ≫
      homPostcompose ((underlying A B C M).obj x)
        ((BimoduleCategory.valueEvaluation A B C y.1.unop y.2).map a) =
    (underlying A B C N).toBimodule.toTensorFunctor.map x y ≫
      homPrecompose ((BimoduleCategory.valueEvaluation A B C x.1.unop x.2).map a)
        ((underlying A B C N).obj y) at h
  have hm (F : BimoduleTensorFunctor A B C) :
      F.toBimodule.toTensorFunctor.map x y = F.map x y := by
    apply tensorHom_ext
    intro p q n hn
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f g
    change (F.toBimodule.uncurryHom x y).f n (dgTensorElement A f g hn) =
      (F.map x y).f n (dgTensorElement A f g hn)
    have hl := congrArg (fun t => t.f q g) (F.toBimodule_map_π x.2 y.2 y.1.unop)
    change F.toBimodule.leftCochain g y.1.unop =
      ((F.leftAt y.1.unop).map x.2 y.2).f q g at hl
    rw [Bimodule.uncurryHom_apply, hl, BimoduleTensorFunctor.map_tensorElement]
    rfl
  rw [hm, hm] at h
  exact h

/-- 両作用に全Hom自然なbimodule射を積dg圏上の加群射へ戻す。 -/
def preimageMap {M N : BimoduleTensorModuleCategory A B C}
    (a : (functor A B C).obj M ⟶ (functor A B C).obj N) : M ⟶ N :=
  leftModuleMorphismMk A (DGTensorCategory A Bᵒᵖ C)
    (M := underlying A B C M) (N := underlying A B C N)
    (fun x => (BimoduleCategory.valueEvaluation A B C x.1.unop x.2).map a)
    (preimage_naturality A B C a)

@[simp]
lemma preimageMap_eval {M N : BimoduleTensorModuleCategory A B C}
    (a : (functor A B C).obj M ⟶ (functor A B C).obj N)
    (x : DGTensorCategory A Bᵒᵖ C) :
    (leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) x).map (preimageMap A B C a) =
      (BimoduleCategory.valueEvaluation A B C x.1.unop x.2).map a :=
  leftModuleMorphismMk_eval A (DGTensorCategory A Bᵒᵖ C) _ _ x

@[simp]
lemma map_preimageMap {M N : BimoduleTensorModuleCategory A B C}
    (a : (functor A B C).obj M ⟶ (functor A B C).obj N) :
    (functor A B C).map (preimageMap A B C a) = a := by
  apply BimoduleCategory.value_hom_ext A B C
  intro b c
  rw [functor_map_value, preimageMap_eval]

@[simp]
lemma preimageMap_map {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) :
    preimageMap A B C ((functor A B C).map f) = f := by
  apply (functor A B C).map_injective
  exact map_preimageMap A B C _

lemma preimageMap_quasiIso_iff {M N : BimoduleTensorModuleCategory A B C}
    (a : (functor A B C).obj M ⟶ (functor A B C).obj N) :
    leftModuleQuasiIso A (DGTensorCategory A Bᵒᵖ C) (preimageMap A B C a) ↔
      BimoduleCategory.quasiIso A B C a := by
  rw [← functor_quasiIso_iff, map_preimageMap]

instance full : (functor A B C).Full where
  map_surjective a := ⟨preimageMap A B C a, map_preimageMap A B C a⟩

instance isEquivalence : (functor A B C).IsEquivalence where
  faithful := faithful A B C
  full := full A B C

/-- 対象だけでなく、全Hom自然な閉零射も含む圏同値。 -/
def equivalence : BimoduleTensorModuleCategory A B C ≌ BimoduleCategory A B C :=
  (functor A B C).asEquivalence

end SerrePositivity.DifferentialGraded.BimoduleTensorModule
end

end TensorModuleFull

/-! ## UncurryClosedFunctor（旧 SerrePositivity/DifferentialGraded/Bimodule/UncurryClosedFunctor.lean） -/

/-! # 全Hom自然な閉零bimodule射の明示的なuncurry関手

## 概要
全Hom自然な閉零bimodule射の明示的なuncurry関手。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section UncurryClosedFunctor
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensorModule
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

/-- 既存のuncurryHom自然性を主Hom endの閉零射へ束ねる。 -/
def uncurryMap {M N : BimoduleCategory A B C} (f : M ⟶ N) :
    objectPreimage A B C M ⟶ objectPreimage A B C N :=
  leftModuleMorphismMk A (DGTensorCategory A Bᵒᵖ C)
    (M := (BimoduleCategory.underlying A B C M).toTensorFunctor)
    (N := (BimoduleCategory.underlying A B C N).toTensorFunctor)
    (fun x => (BimoduleCategory.valueEvaluation A B C x.1.unop x.2).map f)
    (BimoduleCategory.valueMap_uncurry_naturality A B C f)

@[simp]
lemma uncurryMap_eval {M N : BimoduleCategory A B C} (f : M ⟶ N)
    (x : DGTensorCategory A Bᵒᵖ C) :
    (leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) x).map (uncurryMap A B C f) =
      (BimoduleCategory.valueEvaluation A B C x.1.unop x.2).map f :=
  leftModuleMorphismMk_eval A (DGTensorCategory A Bᵒᵖ C) _ _ x

/-- 選択された逆関手を使わない、値と両作用を保持するuncurry。 -/
def uncurryFunctor : BimoduleCategory A B C ⥤ BimoduleTensorModuleCategory A B C where
  obj := objectPreimage A B C
  map := uncurryMap A B C
  map_id M := by
    apply leftModuleMorphism_ext
    intro x
    rw [uncurryMap_eval, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply leftModuleMorphism_ext
    intro x
    rw [uncurryMap_eval, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      uncurryMap_eval, uncurryMap_eval]

/-- uncurryの戻りを、各値で恒等の右加群同型として比較する。 -/
def uncurryRightCounitIso (M : BimoduleCategory A B C) (c : C) :
    (BimoduleCategory.evaluation A B C c).obj ((functor A B C).obj (objectPreimage A B C M)) ≅
      (BimoduleCategory.evaluation A B C c).obj M :=
  moduleIsoMk A B (fun _ => Iso.refl _) (by
    intro x y
    apply hom_naturality_of_apply
    intro p f
    simp only [Iso.refl_hom, CochainComplex.HomComplex.Cochain.comp_id,
      CochainComplex.HomComplex.Cochain.id_comp]
    exact congrArg (fun k => k.f p f)
      ((BimoduleCategory.underlying A B C M).uncurryHom_first c x y))

@[simp]
lemma uncurryRightCounitIso_hom_eval (M : BimoduleCategory A B C) (b : B) (c : C) :
    (moduleEvaluation A B b).map (uncurryRightCounitIso A B C M c).hom = 𝟙 _ :=
  moduleIsoMk_hom_eval A B _ _ b

lemma uncurryRightCounitIso_naturality (M : BimoduleCategory A B C) (c c' : C) :
    (BimoduleCategory.underlying A B C ((functor A B C).obj (objectPreimage A B C M))).map c c' ≫
      moduleHomPostcompose A B
        ((BimoduleCategory.underlying A B C M).toTensorFunctor.toBimodule.rightAt c)
        ((BimoduleCategory.underlying A B C M).toTensorFunctor.toBimodule.rightAt c')
        ((BimoduleCategory.underlying A B C M).rightAt c')
        (uncurryRightCounitIso A B C M c').hom =
    (BimoduleCategory.underlying A B C M).map c c' ≫
      moduleHomPrecompose A B
        ((BimoduleCategory.underlying A B C M).toTensorFunctor.toBimodule.rightAt c)
        ((BimoduleCategory.underlying A B C M).rightAt c)
        ((BimoduleCategory.underlying A B C M).rightAt c')
        (uncurryRightCounitIso A B C M c).hom := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [moduleMorphismComponent, uncurryRightCounitIso_hom_eval]
  have h := (BimoduleCategory.underlying A B C M).toTensorFunctor.toBimodule_map_π c c' b
  have hh := h.trans ((BimoduleCategory.underlying A B C M).uncurryHom_second b c c')
  have hn :
      ((BimoduleCategory.underlying A B C ((functor A B C).obj
          (objectPreimage A B C M))).leftAt b).map c c' ≫ homPostcompose _ (𝟙 _) =
      ((BimoduleCategory.underlying A B C M).leftAt b).map c c' ≫ homPrecompose (𝟙 _) _ := by
    apply hom_naturality_of_apply
    intro p f
    refine (CochainComplex.HomComplex.Cochain.comp_id _).trans ?_
    exact (congrArg (fun k => k.f p f) hh).trans
      (CochainComplex.HomComplex.Cochain.id_comp _).symm
  change (_ ≫ moduleHomπ A B _ _ b) ≫ _ = (_ ≫ moduleHomπ A B _ _ b) ≫ _ at hn
  exact (Category.assoc _ _ _).symm.trans (hn.trans (Category.assoc _ _ _))

def uncurryObjectCounitIso (M : BimoduleCategory A B C) :
    (functor A B C).obj (objectPreimage A B C M) ≅ M :=
  BimoduleCategory.isoOfFamily A B C (uncurryRightCounitIso A B C M)
    (uncurryRightCounitIso_naturality A B C M)

@[simp]
lemma uncurryObjectCounitIso_hom_value (M : BimoduleCategory A B C) (b : B) (c : C) :
    (BimoduleCategory.valueEvaluation A B C b c).map (uncurryObjectCounitIso A B C M).hom = 𝟙 _ :=
  uncurryRightCounitIso_hom_eval A B C M b c

/-- 明示的uncurryから主bimoduleへの戻りは恒等関手と自然同型。 -/
def uncurryCounitIso : uncurryFunctor A B C ⋙ functor A B C ≅ 𝟭 (BimoduleCategory A B C) :=
  NatIso.ofComponents (uncurryObjectCounitIso A B C) (by
    intro M N f
    apply BimoduleCategory.value_hom_ext A B C
    intro b c
    simp only [Functor.comp_map, Functor.id_map, CategoryTheory.Functor.map_comp,
      functor_map_value, uncurryFunctor, uncurryMap_eval]
    rw [uncurryObjectCounitIso_hom_value A B C N b c,
      uncurryObjectCounitIso_hom_value A B C M b c]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

end SerrePositivity.DifferentialGraded.BimoduleTensorModule
end

end UncurryClosedFunctor

/-! ## RightModuleComparison（旧 SerrePositivity/DifferentialGraded/Bimodule/RightModuleComparison.lean） -/

/-! # 積dg圏のopposite上の右加群とbimoduleの比較

## 概要
積dg圏のopposite上の右加群とbimoduleの比較。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/RightRestriction.lean、Bimodule/
SemifreeResolution.lean。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RightModuleComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 既存semifree解像度の圏から、全Hom自然な主bimodule圏への同値。 -/
def rightModuleBimoduleEquivalence :
    ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ ≌ BimoduleCategory A B C :=
  (leftRightOppositeEquivalence A (DGTensorCategory A Bᵒᵖ C)).symm.trans
    (BimoduleTensorModule.equivalence A B C)

/-- 値の評価は元の右加群の積対象での評価と自然同型になる。 -/
def rightModuleBimoduleEvaluationIso (b : B) (c : C) :
    (rightModuleBimoduleEquivalence A B C).functor ⋙
        BimoduleCategory.valueEvaluation A B C b c ≅
      moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (op (op b, c)) := by
  let E := leftRightOppositeEquivalence A (DGTensorCategory A Bᵒᵖ C)
  let V := moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (op (op b, c))
  refine NatIso.ofComponents (fun M => V.mapIso (E.counitIso.app M)) ?_
  intro M N f
  change (BimoduleCategory.valueEvaluation A B C b c).map
      ((BimoduleTensorModule.functor A B C).map (E.inverse.map f)) ≫
        V.map (E.counitIso.app N).hom =
    V.map (E.counitIso.app M).hom ≫ V.map f
  rw [BimoduleTensorModule.functor_map_value]
  rw [← leftModuleToRightOpposite_map_eval A (DGTensorCategory A Bᵒᵖ C)]
  exact (V.map_comp _ _).symm.trans
    ((congrArg V.map (E.counitIso.hom.naturality f)).trans (V.map_comp _ _))

lemma rightModuleBimoduleEquivalence_quasiIso_iff
    {M N : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ} (f : M ⟶ N) :
    BimoduleCategory.quasiIso A B C ((rightModuleBimoduleEquivalence A B C).functor.map f) ↔
      moduleQuasiIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ f := by
  change BimoduleCategory.quasiIso A B C
    ((BimoduleTensorModule.functor A B C).map
      ((leftRightOppositeEquivalence A (DGTensorCategory A Bᵒᵖ C)).inverse.map f)) ↔ _
  rw [BimoduleTensorModule.functor_quasiIso_iff]
  let E := leftRightOppositeEquivalence A (DGTensorCategory A Bᵒᵖ C)
  let W := moduleQuasiIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
  change W (E.functor.map (E.inverse.map f)) ↔ W f
  calc
    W (E.functor.map (E.inverse.map f)) ↔
        W (E.functor.map (E.inverse.map f) ≫ (E.counitIso.app N).hom) :=
      (W.cancel_right_of_respectsIso _ _).symm
    _ ↔ W ((E.counitIso.app M).hom ≫ f) := by
      exact Iff.of_eq (congrArg (fun k => W k) (E.counitIso.hom.naturality f))
    _ ↔ W f := W.cancel_left_of_respectsIso _ _

end SerrePositivity.DifferentialGraded
end

end RightModuleComparison

/-! ## RightRestriction（旧 SerrePositivity/DifferentialGraded/Bimodule/RightRestriction.lean） -/

/-! # 積dg圏のopposite上の右加群の右B制限

## 概要
積dg圏のopposite上の右加群の右B制限。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/CylinderKFlat.lean、Bimodule/
RestrictedRepresentableAction.lean、Tensor/BimoduleRestrictionKFlat.lean。局所導来合成の計算部品、一般Morita・
相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RightRestriction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 第一因子の包含を二重oppositeへ送り、右加群の制限の向きを固定する。 -/
def tensorRightRestrictionInclusion (c : C) :
    DGFunctor A Bᵒᵖ (DGTensorCategory A Bᵒᵖ C)ᵒᵖᵒᵖ :=
  (dgTensorIncludeFirst A Bᵒᵖ C c).comp (dgDoubleOpposite A (DGTensorCategory A Bᵒᵖ C))

def tensorRightRestriction (c : C) :
    ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ ⥤ ModuleCategory A B :=
  moduleRestriction A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (tensorRightRestrictionInclusion A B C c)

def tensorRightRestrictionEvaluationIso (b : B) (c : C) :
    tensorRightRestriction A B C c ⋙ moduleEvaluation A B b ≅
      moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (op (op b, c)) :=
  moduleRestrictionEvaluationIso A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    (tensorRightRestrictionInclusion A B C c) b

/-- 選択された左右同値の逆を使う主bimoduleの右制限も、直接の制限と同型。 -/
def rightModuleBimoduleRightRestrictionIso
    (M : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) (c : C) :
    (BimoduleCategory.evaluation A B C c).obj
        ((rightModuleBimoduleEquivalence A B C).functor.obj M) ≅
      (tensorRightRestriction A B C c).obj M := by
  let L := leftRightOppositeEquivalence A (DGTensorCategory A Bᵒᵖ C)
  let ε := L.counitIso.app M
  let K := ForgetEnrichment.to (Complex A) (L.inverse.obj M)
  refine moduleIsoMk A B
    (M := (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj M)).rightAt c)
    (N := restrictModule A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      (tensorRightRestrictionInclusion A B C c) (ForgetEnrichment.to (Complex A) M))
    (fun x => (moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (op (x, c))).mapIso ε) ?_
  intro x y
  have h := moduleRestriction_naturality A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    (tensorRightRestrictionInclusion A B C c) ε.hom x y
  change (((dgTensorFirstHom A Bᵒᵖ C c x y) ≫ 𝟙 _) ≫
      (𝟙 _ ≫ K.map (x, c) (y, c))) ≫ _ =
    (((dgTensorFirstHom A Bᵒᵖ C c x y) ≫ 𝟙 _) ≫
      (ForgetEnrichment.to (Complex A) M).map (op (op (x, c))) (op (op (y, c)))) ≫ _ at h
  simp only [Category.comp_id, Category.id_comp] at h
  exact h

end SerrePositivity.DifferentialGraded
end

end RightRestriction

/-! ## RightRestrictionNaturality（旧 SerrePositivity/DifferentialGraded/Bimodule/RightRestrictionNaturality.lean） -/

/-! # 積dg圏表示の右制限比較の射に関する自然性

## 概要
積dg圏表示の右制限比較の射に関する自然性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RightRestrictionNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

def rightModuleBimoduleRightRestrictionNatIso (c : C) :
    (rightModuleBimoduleEquivalence A B C).functor ⋙ BimoduleCategory.evaluation A B C c ≅
      tensorRightRestriction A B C c :=
  NatIso.ofComponents (fun M => rightModuleBimoduleRightRestrictionIso A B C M c) (by
    intro M N f
    apply moduleMorphism_ext
    intro b
    simp only [CategoryTheory.Functor.map_comp, rightModuleBimoduleRightRestrictionIso,
      moduleIsoMk_hom_eval, tensorRightRestriction, moduleRestriction_map_eval]
    have h := (rightModuleBimoduleEvaluationIso A B C b c).hom.naturality f
    exact h)

lemma rightModuleBimoduleRightRestrictionNatIso_app (c : C)
    (M : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) :
    (rightModuleBimoduleRightRestrictionNatIso A B C c).app M =
      rightModuleBimoduleRightRestrictionIso A B C M c := rfl

end SerrePositivity.DifferentialGraded
end

end RightRestrictionNaturality

/-! ## SemifreeResolution（旧 SerrePositivity/DifferentialGraded/Bimodule/SemifreeResolution.lean） -/

/-! # 任意bimoduleの積dg圏上のsemifree解像度

## 概要
任意bimoduleの積dg圏上のsemifree解像度。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleSemifreeComparison.lean、Tensor/
BimoduleRestrictionKFlat.lean。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section SemifreeResolution
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 積dg圏のopposite上の実際のfiltrationと主bimoduleへの準同型を保持する。
各右制限のsemifree性や相対K-flat性はこの定義には含めない。 -/
structure BimoduleSemifreeResolution (M : BimoduleCategory A B C) where
  source : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
  filtration : ModuleSemifreeFiltration A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ source
  π : (rightModuleBimoduleEquivalence A B C).functor.obj source ⟶ M
  quasiIso : BimoduleCategory.quasiIso A B C π

namespace BimoduleSemifreeResolution
variable {A B C} {M : BimoduleCategory A B C}

/-- 両作用に全Hom自然な主bimodule圏の対象としての解像度。 -/
def obj (P : BimoduleSemifreeResolution A B C M) : BimoduleCategory A B C :=
  (rightModuleBimoduleEquivalence A B C).functor.obj P.source

lemma semifree (P : BimoduleSemifreeResolution A B C M) :
    moduleSemifree A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ P.source :=
  ⟨P.filtration⟩

lemma value_quasiIso (P : BimoduleSemifreeResolution A B C M) (b : B) (c : C) :
    QuasiIso ((BimoduleCategory.valueEvaluation A B C b c).map P.π) :=
  P.quasiIso b c

end BimoduleSemifreeResolution

/-- 既存の可算cell解像度を圏同値で運ぶ。元のfiltrationの証拠を保持する。 -/
def bimoduleCanonicalSemifreeResolution (M : BimoduleCategory A B C) :
    BimoduleSemifreeResolution A B C M where
  source := moduleResolutionCandidate A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    ((rightModuleBimoduleEquivalence A B C).inverse.obj M)
  filtration := moduleResolutionSemifreeFiltration A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    ((rightModuleBimoduleEquivalence A B C).inverse.obj M)
  π := (rightModuleBimoduleEquivalence A B C).functor.map
    (moduleResolutionCandidateπ A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      ((rightModuleBimoduleEquivalence A B C).inverse.obj M)) ≫
    ((rightModuleBimoduleEquivalence A B C).counitIso.app M).hom
  quasiIso := (BimoduleCategory.quasiIso A B C).comp_mem _ _
    ((rightModuleBimoduleEquivalence_quasiIso_iff A B C _).2
      (moduleResolutionCandidateπ_quasiIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ _))
    ((BimoduleCategory.quasiIso A B C).of_isIso _)

theorem exists_semifree_bimodule_resolution (M : BimoduleCategory A B C) :
    Nonempty (BimoduleSemifreeResolution A B C M) :=
  ⟨bimoduleCanonicalSemifreeResolution A B C M⟩

end SerrePositivity.DifferentialGraded
end

end SemifreeResolution

/-! ## SemifreeRetarget（旧 SerrePositivity/DifferentialGraded/Bimodule/SemifreeRetarget.lean） -/

/-! # 準同型による増大の後合成でsemifree解像度の終域を替える

## 概要
準同型による増大の後合成でsemifree解像度の終域を替える。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section SemifreeRetarget
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

/-- sourceとfiltrationを保持し、増大を指定準同型で後合成する。 -/
def postcompose {M N : BimoduleCategory A B C} (R : BimoduleSemifreeResolution A B C M)
    (f : M ⟶ N) (hf : BimoduleCategory.quasiIso A B C f) :
    BimoduleSemifreeResolution A B C N where
  source := R.source
  filtration := R.filtration
  π := R.π ≫ f
  quasiIso := (BimoduleCategory.quasiIso A B C).comp_mem _ _ R.quasiIso hf

lemma postcompose_obj {M N : BimoduleCategory A B C} (R : BimoduleSemifreeResolution A B C M)
    (f : M ⟶ N) (hf : BimoduleCategory.quasiIso A B C f) :
    (postcompose A B C R f hf).obj = R.obj := rfl

end SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution
end

end SemifreeRetarget

/-! ## MiddleRestrictionUncurry（旧 SerrePositivity/DifferentialGraded/Bimodule/MiddleRestrictionUncurry.lean） -/

/-! # 中間dg圏の左右制限のuncurryHomと積dg関手のHom写像

## 概要
中間dg圏の左右制限のuncurryHomと積dg関手のHom写像。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section MiddleRestrictionUncurry
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)

omit [Small.{u} C] [Small.{u} D] [DGCategory A E] in
lemma leftRestriction_uncurryHom (P : Bimodule A B C) (x y : DGTensorCategory A Bᵒᵖ D) :
    (leftRestriction A B C D F P).uncurryHom x y =
      (𝟙 (x.1 ⟶[Complex A] y.1) ⊗ₘ F.map x.2 y.2) ≫
        P.uncurryHom (x.1, F.obj x.2) (y.1, F.obj y.2) := by
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change ((leftRestriction A B C D F P).uncurryHom x y).f n (dgTensorElement A f g hn) =
    (P.uncurryHom (x.1, F.obj x.2) (y.1, F.obj y.2)).f n
      ((𝟙 (x.1 ⟶[Complex A] y.1) ⊗ₘ F.map x.2 y.2).f n (dgTensorElement A f g hn))
  have ht := tensorMap_apply (𝟙 (x.1 ⟶[Complex A] y.1)) (F.map x.2 y.2) p q n hn f g
  change (𝟙 (x.1 ⟶[Complex A] y.1) ⊗ₘ F.map x.2 y.2).f n
    (dgTensorElement A f g hn) = dgTensorElement A (x := (x.1, F.obj x.2)) (y := (y.1, F.obj y.2))
      f ((F.map x.2 y.2).f q g) hn at ht
  have he := congrArg (fun t => (P.uncurryHom (x.1, F.obj x.2) (y.1, F.obj y.2)).f n t) ht
  refine Eq.trans ?_ he.symm
  rw [uncurryHom_apply, uncurryHom_apply]
  rfl

lemma rightRestriction_uncurryHom (Q : Bimodule A C E) (x y : DGTensorCategory A Dᵒᵖ E) :
    (rightRestriction A C D E F Q).uncurryHom x y =
      (F.op.map x.1 y.1 ⊗ₘ 𝟙 (x.2 ⟶[Complex A] y.2)) ≫
        Q.uncurryHom (F.op.obj x.1, x.2) (F.op.obj y.1, y.2) := by
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change ((rightRestriction A C D E F Q).uncurryHom x y).f n (dgTensorElement A f g hn) =
    (Q.uncurryHom (F.op.obj x.1, x.2) (F.op.obj y.1, y.2)).f n
      ((F.op.map x.1 y.1 ⊗ₘ 𝟙 (x.2 ⟶[Complex A] y.2)).f n (dgTensorElement A f g hn))
  have ht := tensorMap_apply (F.op.map x.1 y.1) (𝟙 (x.2 ⟶[Complex A] y.2)) p q n hn f g
  change (F.op.map x.1 y.1 ⊗ₘ 𝟙 (x.2 ⟶[Complex A] y.2)).f n
    (dgTensorElement A f g hn) =
      dgTensorElement A (x := (F.op.obj x.1, x.2)) (y := (F.op.obj y.1, y.2))
      ((F.op.map x.1 y.1).f p f) g hn at ht
  have he := congrArg (fun t => (Q.uncurryHom (F.op.obj x.1, x.2) (F.op.obj y.1, y.2)).f n t) ht
  refine Eq.trans ?_ he.symm
  rw [uncurryHom_apply, uncurryHom_apply]
  have hl : (rightRestriction A C D E F Q).leftCochain g y.1.unop =
      Q.leftCochain g (F.obj y.1.unop) :=
    congrArg (fun k => k.f q g) (rightRestriction_leftAt_map A C D E F Q y.1.unop x.2 y.2)
  rw [hl]
  rfl

end SerrePositivity.DifferentialGraded.Bimodule
end

end MiddleRestrictionUncurry

/-! ## PairedRestriction（旧 SerrePositivity/DifferentialGraded/Bimodule/PairedRestriction.lean） -/

/-! # 両端のdg関手に沿う直接制限と全Hom作用

## 概要
両端のdg関手に沿う直接制限と全Hom作用。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PairedRestriction
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D B) (G : DGFunctor A E C)

/-- 左作用、次に右作用を制限する直接の両端制限。 -/
def BimoduleCategory.pairedRestrictionFunctor : BimoduleCategory A B C ⥤ BimoduleCategory A D E :=
  BimoduleCategory.middleLeftRestrictionFunctor A B C E G ⋙
    BimoduleCategory.middleRightRestrictionFunctor A B D E F

lemma Bimodule.pairedRestriction_uncurryHom (P : Bimodule A B C)
    (x y : DGTensorCategory A Dᵒᵖ E) :
    (Bimodule.rightRestriction A B D E F (Bimodule.leftRestriction A B C E G P)).uncurryHom x y =
      (F.op.map x.1 y.1 ⊗ₘ G.map x.2 y.2) ≫
        P.uncurryHom (F.op.obj x.1, G.obj x.2) (F.op.obj y.1, G.obj y.2) := by
  rw [Bimodule.rightRestriction_uncurryHom, Bimodule.leftRestriction_uncurryHom,
    tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]

lemma BimoduleCategory.pairedRestrictionFunctor_map_value
    {P Q : BimoduleCategory A B C} (q : P ⟶ Q) (d : D) (e : E) :
    (BimoduleCategory.valueEvaluation A D E d e).map
        ((BimoduleCategory.pairedRestrictionFunctor A B C D E F G).map q) =
      (BimoduleCategory.valueEvaluation A B C (F.obj d) (G.obj e)).map q :=
  (BimoduleCategory.middleRightRestrictionMap_value_eval A B D E F
    ((BimoduleCategory.middleLeftRestrictionFunctor A B C E G).map q) d e).trans
      (BimoduleCategory.middleLeftRestrictionMap_value_eval A B C E G q (F.obj d) e)

lemma Bimodule.pairedRestriction_interchange (P : Bimodule A B C) :
    Bimodule.rightRestriction A B D E F (Bimodule.leftRestriction A B C E G P) =
      Bimodule.leftRestriction A D C E G (Bimodule.rightRestriction A B D C F P) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := Bimodule.rightRestriction A B D E F (Bimodule.leftRestriction A B C E G P))
    (G := Bimodule.leftRestriction A D C E G (Bimodule.rightRestriction A B D C F P))
    (fun _ => rfl)
  intro e e'
  simp only [eqToHom_refl, Category.comp_id]
  change (G.map e e' ≫ P.map (G.obj e) (G.obj e')) ≫
      moduleRestrictionHom A D B F.op _ _ =
    G.map e e' ≫ (P.map (G.obj e) (G.obj e') ≫ moduleRestrictionHom A D B F.op _ _)
  exact Category.assoc _ _ _

/-- 直接左右制限の順序を交換する、右加群ごとに恒等の比較。 -/
def BimoduleCategory.pairedRestrictionInterchangeObjIso (P : BimoduleCategory A B C) :
    (BimoduleCategory.pairedRestrictionFunctor A B C D E F G).obj P ≅
      (BimoduleCategory.middleLeftRestrictionFunctor A D C E G).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj P) :=
  eqToIso (Bimodule.pairedRestriction_interchange A B C D E F G _)

@[simp]
lemma BimoduleCategory.pairedRestrictionInterchangeObjIso_hom_eval
    (P : BimoduleCategory A B C) (e : E) :
    (BimoduleCategory.evaluation A D E e).map
        (BimoduleCategory.pairedRestrictionInterchangeObjIso A B C D E F G P).hom = 𝟙 _ := by
  simp only [BimoduleCategory.pairedRestrictionInterchangeObjIso, eqToIso.hom, eqToHom_map]
  rfl

/-- 直接左右制限の交換は任意の閉零bimodule射に自然。 -/
def BimoduleCategory.pairedRestrictionInterchangeIso :
    BimoduleCategory.pairedRestrictionFunctor A B C D E F G ≅
      BimoduleCategory.middleRightRestrictionFunctor A B D C F ⋙
        BimoduleCategory.middleLeftRestrictionFunctor A D C E G :=
  NatIso.ofComponents (BimoduleCategory.pairedRestrictionInterchangeObjIso A B C D E F G) (by
    intro P Q q
    apply BimoduleCategory.hom_ext
    intro e
    simp only [CategoryTheory.Functor.map_comp,
      BimoduleCategory.pairedRestrictionInterchangeObjIso_hom_eval, Functor.comp_map]
    change (moduleRestriction A D B F.op).map (q.val (G.obj e)) ≫ 𝟙 _ =
      𝟙 _ ≫ (moduleRestriction A D B F.op).map (q.val (G.obj e))
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

end SerrePositivity.DifferentialGraded
end

end PairedRestriction

/-! ## PairedRestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Bimodule/PairedRestrictionCoherence.lean） -/

/-! # 直接の両端制限の恒等・合成比較

## 概要
直接の両端制限の恒等・合成比較。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PairedRestrictionCoherence
universe u v w z t s r

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C]

/-- 恒等の両端制限を、既存の左右の恒等比較で元に戻す。 -/
def pairedRestrictionIdObjIso (P : BimoduleCategory A B C) :
    (pairedRestrictionFunctor A B C B C (DGFunctor.id B) (DGFunctor.id C)).obj P ≅ P :=
  (middleRightRestrictionFunctor A B B C (DGFunctor.id B)).mapIso
      (middleLeftRestrictionIdObjIso A B C P) ≪≫
    middleRightRestrictionIdObjIso A B C P

@[simp]
lemma pairedRestrictionIdObjIso_hom_value (P : BimoduleCategory A B C) (b : B) (c : C) :
    (valueEvaluation A B C b c).map (pairedRestrictionIdObjIso A B C P).hom = 𝟙 _ := by
  simp only [pairedRestrictionIdObjIso, Iso.trans_hom, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp]
  have h := middleRightRestrictionMap_value_eval A B B C (DGFunctor.id B)
    (middleLeftRestrictionIdObjIso A B C P).hom b c
  change (valueEvaluation A B C b c).map
    (middleRightRestrictionMap A B B C (DGFunctor.id B)
      (middleLeftRestrictionIdObjIso A B C P).hom) ≫ _ = _
  rw [h, middleRightRestrictionIdObjIso_hom_value]
  change (moduleEvaluation A B b).map
      ((evaluation A B C c).map (middleLeftRestrictionIdObjIso A B C P).hom) ≫ 𝟙 _ = _
  rw [middleLeftRestrictionIdObjIso_hom_eval, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

def pairedRestrictionIdIso :
    pairedRestrictionFunctor A B C B C (DGFunctor.id B) (DGFunctor.id C) ≅
      𝟭 (BimoduleCategory A B C) :=
  NatIso.ofComponents (pairedRestrictionIdObjIso A B C) (by
    intro P Q q
    change (pairedRestrictionFunctor A B C B C (DGFunctor.id B) (DGFunctor.id C)).map q ≫
      (pairedRestrictionIdObjIso A B C Q).hom = (pairedRestrictionIdObjIso A B C P).hom ≫ q
    apply value_hom_ext A B C
    intro b c
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rw [pairedRestrictionIdObjIso_hom_value A B C Q b c,
      pairedRestrictionIdObjIso_hom_value A B C P b c, pairedRestrictionFunctor_map_value]
    change (valueEvaluation A B C b c).map q ≫ 𝟙 _ =
      𝟙 _ ≫ (valueEvaluation A B C b c).map q
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

variable (E : Type z) [DGCategory A E] [Small.{u} E]
  (L : Type t) [DGCategory A L] (D : Type s) [DGCategory A D] [Small.{u} D]
  (K : Type r) [DGCategory A K] (F : DGFunctor A D E) (G : DGFunctor A E B)
  (H : DGFunctor A K L) (I : DGFunctor A L C)

/-- 二段階の両端制限を合成関手による制限へ送る。左右の交換比較を明示する。 -/
def pairedRestrictionCompObjIso (P : BimoduleCategory A B C) :
    (pairedRestrictionFunctor A E L D K F H).obj
        ((pairedRestrictionFunctor A B C E L G I).obj P) ≅
      (pairedRestrictionFunctor A B C D K (F.comp G) (H.comp I)).obj P :=
  (middleRightRestrictionFunctor A E D K F).mapIso
      (pairedRestrictionInterchangeObjIso A B L E K G H
        ((middleLeftRestrictionFunctor A B C L I).obj P)).symm ≪≫
    middleRightRestrictionCompObjIso A D K E B F G
      ((middleLeftRestrictionFunctor A B L K H).obj
        ((middleLeftRestrictionFunctor A B C L I).obj P)) ≪≫
    (middleRightRestrictionFunctor A B D K (F.comp G)).mapIso
      (middleLeftRestrictionCompObjIso A B K L C H I P)

@[simp]
lemma pairedRestrictionCompObjIso_hom_value (P : BimoduleCategory A B C) (d : D) (k : K) :
    (valueEvaluation A D K d k).map
        (pairedRestrictionCompObjIso A B C E L D K F G H I P).hom = 𝟙 _ := by
  have h₁ := middleRightRestrictionMap_value_eval A E D K F
    (pairedRestrictionInterchangeObjIso A B L E K G H
      ((middleLeftRestrictionFunctor A B C L I).obj P)).inv d k
  have h₃ := middleRightRestrictionMap_value_eval A B D K (F.comp G)
    (middleLeftRestrictionCompObjIso A B K L C H I P).hom d k
  have hv : (evaluation A E K k).map
      (pairedRestrictionInterchangeObjIso A B L E K G H
        ((middleLeftRestrictionFunctor A B C L I).obj P)).inv = 𝟙 _ := by
    simp only [pairedRestrictionInterchangeObjIso, eqToIso.inv, eqToHom_map]
    rfl
  have h₁' : (valueEvaluation A E K (F.obj d) k).map
      (pairedRestrictionInterchangeObjIso A B L E K G H
        ((middleLeftRestrictionFunctor A B C L I).obj P)).inv = 𝟙 _ := by
    change (moduleEvaluation A E (F.obj d)).map
      ((evaluation A E K k).map
        (pairedRestrictionInterchangeObjIso A B L E K G H
          ((middleLeftRestrictionFunctor A B C L I).obj P)).inv) = _
    rw [hv, CategoryTheory.Functor.map_id]
    rfl
  have h₃' : (valueEvaluation A B K ((F.comp G).obj d) k).map
      (middleLeftRestrictionCompObjIso A B K L C H I P).hom = 𝟙 _ := by
    change (moduleEvaluation A B (G.obj (F.obj d))).map
      ((evaluation A B K k).map (middleLeftRestrictionCompObjIso A B K L C H I P).hom) = _
    rw [middleLeftRestrictionCompObjIso_hom_eval, CategoryTheory.Functor.map_id]
    rfl
  simp only [pairedRestrictionCompObjIso, Iso.trans_hom, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp]
  change (valueEvaluation A D K d k).map (middleRightRestrictionMap A E D K F
      (pairedRestrictionInterchangeObjIso A B L E K G H
        ((middleLeftRestrictionFunctor A B C L I).obj P)).inv) ≫
    (valueEvaluation A D K d k).map (middleRightRestrictionCompObjIso A D K E B F G
      ((middleLeftRestrictionFunctor A B L K H).obj
        ((middleLeftRestrictionFunctor A B C L I).obj P))).hom ≫
    (valueEvaluation A D K d k).map (middleRightRestrictionMap A B D K (F.comp G)
      (middleLeftRestrictionCompObjIso A B K L C H I P).hom) = _
  rw [h₁, h₃, h₁', h₃', middleRightRestrictionCompObjIso_hom_value]
  change (𝟙 ((underlying A B C P).value (G.obj (F.obj d)) (I.obj (H.obj k)))) ≫
    𝟙 _ ≫ 𝟙 _ = 𝟙 _
  rw [Category.id_comp, Category.id_comp]

def pairedRestrictionCompIso :
    pairedRestrictionFunctor A B C E L G I ⋙ pairedRestrictionFunctor A E L D K F H ≅
      pairedRestrictionFunctor A B C D K (F.comp G) (H.comp I) :=
  NatIso.ofComponents (pairedRestrictionCompObjIso A B C E L D K F G H I) (by
    intro P Q q
    change ((pairedRestrictionFunctor A B C E L G I ⋙
      pairedRestrictionFunctor A E L D K F H).map q) ≫
      (pairedRestrictionCompObjIso A B C E L D K F G H I Q).hom =
      (pairedRestrictionCompObjIso A B C E L D K F G H I P).hom ≫
      (pairedRestrictionFunctor A B C D K (F.comp G) (H.comp I)).map q
    apply value_hom_ext A D K
    intro d k
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rw [pairedRestrictionCompObjIso_hom_value A B C E L D K F G H I Q d k,
      pairedRestrictionCompObjIso_hom_value A B C E L D K F G H I P d k]
    simp only [Functor.comp_map, pairedRestrictionFunctor_map_value]
    change (valueEvaluation A B C (G.obj (F.obj d)) (I.obj (H.obj k))).map q ≫ 𝟙 _ =
      𝟙 _ ≫ (valueEvaluation A B C (G.obj (F.obj d)) (I.obj (H.obj k))).map q
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

end SerrePositivity.DifferentialGraded.BimoduleCategory
end

end PairedRestrictionCoherence

/-! ## ExplicitRightModuleFunctor（旧 SerrePositivity/DifferentialGraded/Bimodule/ExplicitRightModuleFunctor.lean） -/

/-! # bimoduleの積dg圏上の右加群への明示的関手と選択された逆関手の比較

## 概要
bimoduleの積dg圏上の右加群への明示的関手と選択された逆関手の比較。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section ExplicitRightModuleFunctor
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensorModule
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

def rightModuleFunctor : BimoduleCategory A B C ⥤
    ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ :=
  uncurryFunctor A B C ⋙ leftModuleToRightOpposite A (DGTensorCategory A Bᵒᵖ C)

@[simp]
lemma rightModuleFunctor_map_value {M N : BimoduleCategory A B C} (f : M ⟶ N) (b : B) (c : C) :
    (moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (op (op b, c))).map
        ((rightModuleFunctor A B C).map f) =
      (BimoduleCategory.valueEvaluation A B C b c).map f :=
  (leftModuleToRightOpposite_map_eval A (DGTensorCategory A Bᵒᵖ C)
    ((uncurryFunctor A B C).map f) (op b, c)).trans (uncurryMap_eval A B C f (op b, c))

/-- 明示的な右加群表示から既存の選択された戻り関手へ送ると元のbimoduleに戻る。 -/
def rightModuleCounitIso :
    rightModuleFunctor A B C ⋙ (rightModuleBimoduleEquivalence A B C).functor ≅
      𝟭 (BimoduleCategory A B C) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (uncurryFunctor A B C)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (leftRightOppositeEquivalence A (DGTensorCategory A Bᵒᵖ C)).unitIso.symm
          (functor A B C) ≪≫ Functor.leftUnitor _) ≪≫ uncurryCounitIso A B C

/-- 明示的な右加群表示と、既存の圏同値が選択した逆関手との自然同型。 -/
def rightModuleInverseIso :
    rightModuleFunctor A B C ≅ (rightModuleBimoduleEquivalence A B C).inverse :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (rightModuleFunctor A B C)
      (rightModuleBimoduleEquivalence A B C).unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightModuleCounitIso A B C)
      (rightModuleBimoduleEquivalence A B C).inverse ≪≫ Functor.leftUnitor _

end SerrePositivity.DifferentialGraded.BimoduleTensorModule
end

end ExplicitRightModuleFunctor

/-! ## RestrictedRepresentableAction（旧 SerrePositivity/DifferentialGraded/Bimodule/RestrictedRepresentableAction.lean） -/

/-! # 積dg圏の代表加群を右Bへ制限したときの斉次作用

## 概要
積dg圏の代表加群を右Bへ制限したときの斉次作用。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/RestrictedRepresentable.lean。局所導来合成の計算部品、
一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictedRepresentableAction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

omit [Small.{u} B] [Small.{u} C] in
lemma tensorRightRestrictionInclusion_map (c : C) (x y : Bᵒᵖ) :
    (tensorRightRestrictionInclusion A B C c).map x y = dgTensorFirstHom A Bᵒᵖ C c x y := by
  change dgTensorFirstHom A Bᵒᵖ C c x y ≫ 𝟙 _ = _
  exact Category.comp_id _

omit [Small.{u} B] [Small.{u} C] in
lemma restrictedRepresentable_action (b₀ : B) (c₀ c : C) {x y : Bᵒᵖ}
    {p r s k n : ℤ} (hk : r + s = k) (hn : k + p = n)
    (f : GradedHom A x y p) (h : GradedHom A x.unop b₀ r) (g : GradedHom A c₀ c s) :
    moduleAction A
      (restrictModule A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        (tensorRightRestrictionInclusion A B C c)
        (representable A (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C)))) f
      (ιTensorObj (x.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c) r s k hk (h ⊗ₜ[A] g)) hn =
    ιTensorObj (y.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c) (r + p) s n (by omega)
      (forward A (x := y.unop) (y := x.unop) (z := b₀) f h (by omega) ⊗ₜ[A] g) := by
  rw [restrictModule_action, tensorRightRestrictionInclusion_map, representable_action]
  rw [opposite_forward]
  change (p * k).negOnePow • forward A (D := DGTensorCategory A Bᵒᵖ C)
    (x := ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C))
    (y := ((x, c) : DGTensorCategory A Bᵒᵖ C))
    (z := ((y, c) : DGTensorCategory A Bᵒᵖ C))
    (dgTensorElement A h g hk) ((dgTensorFirstHom A Bᵒᵖ C c x y).f p f) hn = _
  rw [dgTensorFirstHom_apply A Bᵒᵖ C c x y p f]
  rw [dgTensor_forward_of_sum A
    (x := ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C))
    (y := ((x, c) : DGTensorCategory A Bᵒᵖ C))
    (z := ((y, c) : DGTensorCategory A Bᵒᵖ C))
    h g f (unitElement A c).val hk (add_zero p) rfl (add_zero s) hn]
  change (p * k).negOnePow • ((s * p).negOnePow •
    ιTensorObj (y.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c) (r + p) s n (by omega)
      (forward A (D := Bᵒᵖ) (x := op b₀) (y := x) (z := y) h f rfl ⊗ₜ[A]
        forward A (D := C) g (unitElement A c).val (add_zero s))) = _
  rw [unit_forward A g]
  rw [opposite_forward A B (op b₀) x y r p (r + p) rfl h f]
  change (p * k).negOnePow • ((s * p).negOnePow •
    ιTensorObj (y.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c) (r + p) s n (by omega)
      (((r * p).negOnePow • forward A (D := B) (x := y.unop) (y := x.unop)
        (z := b₀) (p := p) (q := r) (n := r + p) f h (by omega)) ⊗ₜ[A] g)) = _
  simp only [Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul, smul_smul]
  simp only [← Units.val_mul, ← Int.negOnePow_add]
  have he : p * k + (s * p + r * p) = 2 * (p * k) := by rw [← hk]; ring
  rw [he, Int.negOnePow_two_mul, Units.val_one, one_smul]

end SerrePositivity.DifferentialGraded
end

end RestrictedRepresentableAction

/-! ## RestrictedRepresentable（旧 SerrePositivity/DifferentialGraded/Bimodule/RestrictedRepresentable.lean） -/

/-! # 積dg圏の代表加群の右制限と自由加群との全Hom自然な同型

## 概要
積dg圏の代表加群の右制限と自由加群との全Hom自然な同型。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/RestrictedFree.lean。局所導来合成の計算部品、一般Morita・
相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictedRepresentable
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

def restrictedRepresentableIso (b₀ : B) (c₀ c : C) :
    (tensorRightRestriction A B C c).obj
        (ForgetEnrichment.of (Complex A)
          (representable A (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C)))) ≅
      (freeAt b₀).obj (c₀ ⟶[Complex A] c) :=
  moduleIsoMk A B
    (M := restrictModule A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      (tensorRightRestrictionInclusion A B C c)
      (representable A (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C))))
    (N := freeModule b₀ (c₀ ⟶[Complex A] c))
    (fun x => signedSwap (x.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c)) (by
      intro x y
      apply hom_naturality_of_apply
      intro p f
      apply Cochain.ext
      intro k n hn
      rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
        Cochain.ofHom_v, Cochain.ofHom_v]
      apply mapBifunctor.hom_ext
      intro r s hk
      change r + s = k at hk
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro h g
      change (signedSwap (y.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c)).hom.f n
        (moduleAction A
          (restrictModule A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
            (tensorRightRestrictionInclusion A B C c)
            (representable A (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C)))) f
          (ιTensorObj (x.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c) r s k hk (h ⊗ₜ[A] g)) hn) =
        moduleAction A (freeModule b₀ (c₀ ⟶[Complex A] c)) f
          ((signedSwap (x.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c)).hom.f k
            (ιTensorObj (x.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c) r s k hk (h ⊗ₜ[A] g))) hn
      rw [restrictedRepresentable_action, signedSwap_apply, signedSwap_apply]
      rw [moduleAction_units_smul]
      rw [tensorModule_action (c₀ ⟶[Complex A] c) (representable A b₀) x y p s r k
        (r + p) n (by omega) rfl hn, representable_action]
      simp only [smul_smul, ← Int.negOnePow_add]
      rw [show (r + p) * s = r * s + p * s by ring])

@[simp]
lemma restrictedRepresentableIso_hom_eval (b₀ : B) (c₀ c : C) (b : B) :
    (moduleEvaluation A B b).map (restrictedRepresentableIso A B C b₀ c₀ c).hom =
      (signedSwap (b ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c)).hom :=
  moduleIsoMk_hom_eval A B _ _ b

@[simp]
lemma restrictedRepresentableIso_inv_eval (b₀ : B) (c₀ c : C) (b : B) :
    (moduleEvaluation A B b).map (restrictedRepresentableIso A B C b₀ c₀ c).inv =
      (signedSwap (b ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c)).inv :=
  moduleIsoMk_inv_eval A B _ _ b

end SerrePositivity.DifferentialGraded
end

end RestrictedRepresentable

/-! ## RestrictedFree（旧 SerrePositivity/DifferentialGraded/Bimodule/RestrictedFree.lean） -/

/-! # 積dg圏上の自由加群の右制限

## 概要
積dg圏上の自由加群の右制限。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Tensor/BimoduleSemifreeKFlat.lean。局所導来合成の計算部品、
一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictedFree
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 制限後の生成複体にはHom_C(c₀,c)が現れる。Hom_Bのflat性は用いない。 -/
def restrictedFreeIso (b₀ : B) (c₀ c : C) (K : Complex A) :
    (tensorRightRestriction A B C c).obj
        ((freeAt (A := A) (D := (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
          (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C))).obj K) ≅
      (freeAt b₀).obj (K ⊗ (c₀ ⟶[Complex A] c)) :=
  moduleRestrictionTensorIso A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      (tensorRightRestrictionInclusion A B C c) K
      (ForgetEnrichment.of (Complex A)
        (representable A (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C)))) ≪≫
    (moduleTensorLeftFunctor A B K).mapIso (restrictedRepresentableIso A B C b₀ c₀ c) ≪≫
    tensorModuleAssociatorIso A B K (c₀ ⟶[Complex A] c) (representable A b₀)

end SerrePositivity.DifferentialGraded
end

end RestrictedFree

/-! ## RelativeKFlat（旧 SerrePositivity/DifferentialGraded/Bimodule/RelativeKFlat.lean） -/

/-! # 右制限の相対K-flat性とbimodule合成による保存

## 概要
右制限の相対K-flat性とbimodule合成による保存。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/CylinderKFlat.lean、Tensor/
BimoduleQuasiIso.lean、Tensor/BimoduleRestrictionKFlat.lean。局所導来合成の計算部品、一般Morita・相対tensor・
Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RelativeKFlat
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 各左対象での右B加群が相対K-flatである条件。A上のobjectwise K-flat性とは別。 -/
def rightRelativeKFlat (P : Bimodule A B C) : Prop :=
  ∀ c : C, moduleRelativeKFlat A B (P.rightAt c)

lemma rightRelativeKFlat_of_iso {P Q : BimoduleCategory A B C} (e : P ≅ Q)
    (h : rightRelativeKFlat A B C (BimoduleCategory.underlying A B C Q)) :
    rightRelativeKFlat A B C (BimoduleCategory.underlying A B C P) := by
  intro c
  exact moduleRelativeKFlat_of_iso A B ((BimoduleCategory.evaluation A B C c).mapIso e) (h c)

lemma rightRelativeKFlat_of_retract {P Q : BimoduleCategory A B C} (e : Retract P Q)
    (h : rightRelativeKFlat A B C (BimoduleCategory.underlying A B C Q)) :
    rightRelativeKFlat A B C (BimoduleCategory.underlying A B C P) := by
  intro c
  exact moduleRelativeKFlat_of_retract A B (e.map (BimoduleCategory.evaluation A B C c)) (h c)

/-- 片側の各制限にsemifree性の証拠がある場合の十分条件。 -/
lemma rightRelativeKFlat_of_rightAt_semifree (P : Bimodule A B C)
    (h : ∀ c, moduleSemifree A B (ForgetEnrichment.of (Complex A) (P.rightAt c))) :
    rightRelativeKFlat A B C P := by
  intro c
  exact moduleSemifree_relativeKFlat A B (h c)

/-- 片側の各制限の全Hom射影性も相対K-flat性を与える。 -/
lemma rightRelativeKFlat_of_rightAt_projective (P : Bimodule A B C)
    (h : ∀ c, moduleHomotopicallyProjective A B
      (ForgetEnrichment.of (Complex A) (P.rightAt c))) : rightRelativeKFlat A B C P := by
  intro c
  exact moduleHomotopicallyProjective_relativeKFlat A B (h c)

lemma diagonal_rightRelativeKFlat : rightRelativeKFlat A B B (diagonal A B) :=
  fun b => representable_relativeKFlat A B b

variable [Small.{u} C] (E : Type z) [DGCategory A E]

/-- Fubiniにより、右制限が相対K-flatな二つのbimoduleの合成も同じ条件を満たす。 -/
lemma rightRelativeKFlat_compose (P : Bimodule A B C) (Q : Bimodule A C E)
    (hP : rightRelativeKFlat A B C P) (hQ : rightRelativeKFlat A C E Q) :
    rightRelativeKFlat A B E (BimoduleTensor.compose A B C E P Q) := by
  intro e N hN
  have hL : leftModuleAcyclic A C (BalancedTensor.Fubini.leftModule A B C P N) :=
    fun c => hP c N hN
  have h := hQ e (BalancedTensor.Fubini.leftModule A B C P N) hL
  exact cochainAcyclic_of_iso h (BalancedTensor.Fubini.iso A B C P (Q.rightAt e) N)

end SerrePositivity.DifferentialGraded.Bimodule
end

end RelativeKFlat

/-! ## CylinderKFlat（旧 SerrePositivity/DifferentialGraded/Bimodule/CylinderKFlat.lean） -/

/-! # 積dg圏上のcylinderをbimoduleへ移送したときの右相対K-flat性

## 概要
積dg圏上のcylinderをbimoduleへ移送したときの右相対K-flat性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleHomotopy.lean。局所導来合成の計算部品、
一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CylinderKFlat
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma rightModuleBimodule_cylinder_rightRelativeKFlat
    (M : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
    (hM : Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj M))) :
    Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj
        (modulePrecylinder A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ M).I)) := by
  intro c
  have hr := moduleRelativeKFlat_of_iso A B
    (rightModuleBimoduleRightRestrictionIso A B C M c).symm (hM c)
  have ht := moduleRelativeKFlat_tensor A B (dgInterval A) (complexKFlat_interval A)
    (ForgetEnrichment.to (Complex A) ((tensorRightRestriction A B C c).obj M)) hr
  exact moduleRelativeKFlat_of_iso A B
    (rightModuleBimoduleRightRestrictionIso A B C
        (modulePrecylinder A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ M).I c ≪≫
      moduleRestrictionTensorIso A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        (tensorRightRestrictionInclusion A B C c) (dgInterval A) M) ht

end SerrePositivity.DifferentialGraded
end

end CylinderKFlat
