module
public import SerrePositivity.DifferentialGraded.Bimodule.CylinderKFlat
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleLocalization

/-! # K-flat部分圏の局所化で全dg自然な加群ホモトピーを同一視する

## 概要
K-flat部分圏の局所化で全dg自然な加群ホモトピーを同一視する。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleReplacement.lean。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

def rightKFlatOfModule (M : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
    (hM : Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj M))) : RightKFlatBimoduleCategory A B C :=
  ⟨(rightModuleBimoduleEquivalence A B C).functor.obj M, hM⟩

def rightKFlatOfModuleMap {M N : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ}
    (hM) (hN) (f : M ⟶ N) : rightKFlatOfModule A B C M hM ⟶ rightKFlatOfModule A B C N hN :=
  ObjectProperty.homMk ((rightModuleBimoduleEquivalence A B C).functor.map f)

lemma rightKFlatOfModuleMap_id (M : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) (hM) :
    rightKFlatOfModuleMap A B C hM hM (𝟙 M) = 𝟙 (rightKFlatOfModule A B C M hM) := by
  apply ObjectProperty.hom_ext
  exact (rightModuleBimoduleEquivalence A B C).functor.map_id M

lemma rightKFlatOfModuleMap_comp {M N P : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ}
    (hM) (hN) (hP) (f : M ⟶ N) (g : N ⟶ P) :
    rightKFlatOfModuleMap A B C hM hP (f ≫ g) =
      rightKFlatOfModuleMap A B C hM hN f ≫ rightKFlatOfModuleMap A B C hN hP g := by
  apply ObjectProperty.hom_ext
  exact (rightModuleBimoduleEquivalence A B C).functor.map_comp f g

lemma rightKFlat_equalizes_source_boundary
    {M N : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ}
    (hM : Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj M)))
    (hN : Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj N)))
    (f g : M ⟶ N) (h : boundaryRelation A (RightModule A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) f g) :
    (rightKFlatToDerived A B C).map (rightKFlatOfModuleMap A B C hM hN f) =
      (rightKFlatToDerived A B C).map (rightKFlatOfModuleMap A B C hM hN g) := by
  let P := modulePrecylinder A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ M
  let hI := rightModuleBimodule_cylinder_rightRelativeKFlat A B C M hM
  let i₀ := rightKFlatOfModuleMap A B C hM hI P.i₀
  let i₁ := rightKFlatOfModuleMap A B C hM hI P.i₁
  let π := rightKFlatOfModuleMap A B C hI hM P.π
  let d := rightKFlatOfModuleMap A B C hI hN (moduleCylinderDesc A _ f g h)
  have h₀π : i₀ ≫ π = 𝟙 (rightKFlatOfModule A B C M hM) := by
    rw [← rightKFlatOfModuleMap_comp, P.i₀_π, rightKFlatOfModuleMap_id]
  have h₁π : i₁ ≫ π = 𝟙 (rightKFlatOfModule A B C M hM) := by
    rw [← rightKFlatOfModuleMap_comp, P.i₁_π, rightKFlatOfModuleMap_id]
  have h₀d : i₀ ≫ d = rightKFlatOfModuleMap A B C hM hN f := by
    rw [← rightKFlatOfModuleMap_comp, moduleCylinderDesc_i₀]
  have h₁d : i₁ ≫ d = rightKFlatOfModuleMap A B C hM hN g := by
    rw [← rightKFlatOfModuleMap_comp, moduleCylinderDesc_i₁]
  have hπ : rightKFlatQuasiIso A B C π :=
    (rightModuleBimoduleEquivalence_quasiIso_iff A B C P.π).2
      (modulePrecylinder_π_quasiIso A _ M)
  let e := Localization.Construction.wIso (W := rightKFlatQuasiIso A B C) π hπ
  have hi : (rightKFlatToDerived A B C).map i₀ = (rightKFlatToDerived A B C).map i₁ := by
    apply (Iso.cancel_iso_hom_right _ _ e).1
    exact ((rightKFlatToDerived A B C).map_comp i₀ π).symm.trans
      ((congrArg (rightKFlatToDerived A B C).map h₀π).trans
        ((congrArg (rightKFlatToDerived A B C).map h₁π.symm).trans
          ((rightKFlatToDerived A B C).map_comp i₁ π)))
  calc
    _ = (rightKFlatToDerived A B C).map (i₀ ≫ d) := congrArg _ h₀d.symm
    _ = (rightKFlatToDerived A B C).map i₀ ≫ (rightKFlatToDerived A B C).map d :=
      (rightKFlatToDerived A B C).map_comp _ _
    _ = (rightKFlatToDerived A B C).map i₁ ≫ (rightKFlatToDerived A B C).map d :=
      congrArg (fun k => k ≫ (rightKFlatToDerived A B C).map d) hi
    _ = _ := ((rightKFlatToDerived A B C).map_comp i₁ d).symm.trans (congrArg _ h₁d)

lemma rightKFlat_map_eq_of_source_homotopy
    {M N : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ}
    (hM : Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj M)))
    (hN : Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj N)))
    (f g : M ⟶ N)
    (h : (moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ).map f =
      (moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ).map g) :
    (rightKFlatToDerived A B C).map (rightKFlatOfModuleMap A B C hM hN f) =
      (rightKFlatToDerived A B C).map (rightKFlatOfModuleMap A B C hM hN g) :=
  rightKFlat_equalizes_source_boundary A B C hM hN f g
    ((moduleHomotopy_nonempty_iff A _ f g).1 ((moduleToHomotopy_map_eq_iff A _ f g).1 h))

end SerrePositivity.DifferentialGraded.BimoduleTensor
