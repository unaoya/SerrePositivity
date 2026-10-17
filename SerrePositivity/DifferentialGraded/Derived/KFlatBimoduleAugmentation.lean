module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleReplacement

/-! # K-flat部分圏の局所化内での置換増大射の自然性

## 概要
K-flat部分圏の局所化内での置換増大射の自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleGlobalAugmentation.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
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

def rightKFlatAugmentation (hC : localHomKFlat A C) (M : RightKFlatBimoduleCategory A B C) :
    rightKFlatResolutionObj A B C hC M.obj ⟶ M :=
  ObjectProperty.homMk (bimoduleCanonicalSemifreeResolution A B C M.obj).π

lemma rightKFlat_inverse_rightRelativeKFlat (M : RightKFlatBimoduleCategory A B C) :
    Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj
        ((rightModuleBimoduleEquivalence A B C).inverse.obj M.obj))) :=
  Bimodule.rightRelativeKFlat_of_iso A B C
    ((rightModuleBimoduleEquivalence A B C).counitIso.app M.obj) M.property

lemma rightKFlatAugmentation_naturality (hC : localHomKFlat A C)
    {M N : RightKFlatBimoduleCategory A B C} (f : M ⟶ N) :
    (rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC f.hom) ≫
        (rightKFlatToDerived A B C).map (rightKFlatAugmentation A B C hC N) =
      (rightKFlatToDerived A B C).map (rightKFlatAugmentation A B C hC M) ≫
        (rightKFlatToDerived A B C).map f := by
  let H := rightModuleBimoduleEquivalence A B C
  let R := bimoduleSourceProjectiveResolution A B C
  let K := moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
  let hN := rightKFlat_inverse_rightRelativeKFlat A B C N
  let ε : rightKFlatOfModule A B C (H.inverse.obj N.obj) hN ⟶ N :=
    ObjectProperty.homMk (H.counitIso.app N.obj).hom
  have hs : K.map ((R M.obj).lift (R N.obj) (H.inverse.map f.hom) ≫ (R N.obj).π) =
      K.map ((R M.obj).π ≫ H.inverse.map f.hom) :=
    (K.map_comp _ _).trans
      (((R M.obj).lift_fac (R N.obj) (H.inverse.map f.hom)).trans (K.map_comp _ _).symm)
  have he := rightKFlat_map_eq_of_source_homotopy A B C
    (rightKFlatResolutionObj A B C hC M.obj).property hN _ _ hs
  have hl : rightKFlatOfModuleMap A B C
        (rightKFlatResolutionObj A B C hC M.obj).property hN
        ((R M.obj).lift (R N.obj) (H.inverse.map f.hom) ≫ (R N.obj).π) ≫ ε =
      rightKFlatReplacementMap A B C hC f.hom ≫ rightKFlatAugmentation A B C hC N := by
    apply ObjectProperty.hom_ext
    change H.functor.map (_ ≫ _) ≫ (H.counitIso.app N.obj).hom =
      H.functor.map _ ≫ (H.functor.map (R N.obj).π ≫ (H.counitIso.app N.obj).hom)
    rw [H.functor.map_comp, Category.assoc]
  have hr : rightKFlatOfModuleMap A B C
        (rightKFlatResolutionObj A B C hC M.obj).property hN
        ((R M.obj).π ≫ H.inverse.map f.hom) ≫ ε =
      rightKFlatAugmentation A B C hC M ≫ f := by
    apply ObjectProperty.hom_ext
    change H.functor.map ((R M.obj).π ≫ H.inverse.map f.hom) ≫
      (H.counitIso.app N.obj).hom =
        (H.functor.map (R M.obj).π ≫ (H.counitIso.app M.obj).hom) ≫ f.hom
    rw [H.functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (fun k => H.functor.map (R M.obj).π ≫ k) (H.counitIso.hom.naturality f.hom)
  have hh := congrArg (fun k => k ≫ (rightKFlatToDerived A B C).map ε) he
  rw [← CategoryTheory.Functor.map_comp, hl, ← CategoryTheory.Functor.map_comp, hr] at hh
  exact ((rightKFlatToDerived A B C).map_comp _ _).symm.trans
    (hh.trans ((rightKFlatToDerived A B C).map_comp _ _))

def rightKFlatAugmentationIso (hC : localHomKFlat A C) :
    rightKFlatInclusion A B C ⋙ rightKFlatReplacementFunctor A B C hC ≅
      rightKFlatToDerived A B C :=
  NatIso.ofComponents
    (fun M => Localization.Construction.wIso (W := rightKFlatQuasiIso A B C)
      (rightKFlatAugmentation A B C hC M)
      (bimoduleCanonicalSemifreeResolution A B C M.obj).quasiIso)
    (fun f => rightKFlatAugmentation_naturality A B C hC f)

end SerrePositivity.DifferentialGraded.BimoduleTensor
