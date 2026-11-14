module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGModuleQuasiIsoSurjectiveSpan
public import SerrePositivity.DifferentialGraded.Bimodule.Right
/-!
概要：同じ右加群 disk span を、全 Hom 自然な双加群の実 span へ移す。
方針：実同値と余単位を通じ、元の射を回収する同じ切断も構成する。
規約：二つの脚は同じ中間双加群を持つ。使われ方：任意の核準同型の導来比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w)
  [DGCategory R B] [DGCategory R C] [Small.{u} B] [Small.{u} C]
/-- 同じ実右加群 span の中間双加群。 -/
def dgBimoduleQuasiIsoSpanObject (P Q : BimoduleCategory R B C) : BimoduleCategory R B C :=
  (rightModuleBimoduleEquivalence R B C).functor.obj
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanObject R (DGTensorCategory R Bᵒᵖ C)ᵒᵖ
      ((rightModuleBimoduleEquivalence R B C).inverse.obj P)
      ((rightModuleBimoduleEquivalence R B C).inverse.obj Q))
/-- 同じ実 span から元の始域への左脚。 -/
def dgBimoduleQuasiIsoSpanLeft (P Q : BimoduleCategory R B C) :
    dgBimoduleQuasiIsoSpanObject R B C P Q ⟶ P :=
  (rightModuleBimoduleEquivalence R B C).functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanLeft R (DGTensorCategory R Bᵒᵖ C)ᵒᵖ
      ((rightModuleBimoduleEquivalence R B C).inverse.obj P)
      ((rightModuleBimoduleEquivalence R B C).inverse.obj Q)) ≫
    ((rightModuleBimoduleEquivalence R B C).counitIso.app P).hom
/-- 元の指定射を使う同じ実 span の右脚。 -/
def dgBimoduleQuasiIsoSpanRight {P Q : BimoduleCategory R B C} (f : P ⟶ Q) :
    dgBimoduleQuasiIsoSpanObject R B C P Q ⟶ Q :=
  (rightModuleBimoduleEquivalence R B C).functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanRight R (DGTensorCategory R Bᵒᵖ C)ᵒᵖ
      ((rightModuleBimoduleEquivalence R B C).inverse.map f)) ≫
    ((rightModuleBimoduleEquivalence R B C).counitIso.app Q).hom
/-- 元の始域から同じ実 span への切断。 -/
def dgBimoduleQuasiIsoSpanSection (P Q : BimoduleCategory R B C) :
    P ⟶ dgBimoduleQuasiIsoSpanObject R B C P Q :=
  ((rightModuleBimoduleEquivalence R B C).counitIso.app P).inv ≫
    (rightModuleBimoduleEquivalence R B C).functor.map
      (moduleBiprodInl R (DGTensorCategory R Bᵒᵖ C)ᵒᵖ
        ((rightModuleBimoduleEquivalence R B C).inverse.obj P)
        (moduleDiskCover R (DGTensorCategory R Bᵒᵖ C)ᵒᵖ
          ((rightModuleBimoduleEquivalence R B C).inverse.obj Q)))
/-- 同じ切断と左脚の合成は恒等射。 -/
lemma dgBimoduleQuasiIsoSpanSection_left (P Q : BimoduleCategory R B C) :
    dgBimoduleQuasiIsoSpanSection R B C P Q ≫ dgBimoduleQuasiIsoSpanLeft R B C P Q = 𝟙 P := by
  let E := rightModuleBimoduleEquivalence R B C
  let M := E.inverse.obj P
  let N := E.inverse.obj Q
  change ((E.counitIso.app P).inv ≫ E.functor.map
    (moduleBiprodInl R _ M (moduleDiskCover R _ N))) ≫
      E.functor.map (moduleBiprodFst R _ M (moduleDiskCover R _ N)) ≫ _ = _
  rw [Category.assoc, ← E.functor.map_comp_assoc]
  have h := (moduleBinaryBicone R (DGTensorCategory R Bᵒᵖ C)ᵒᵖ M
    (moduleDiskCover R _ N)).inl_fst
  change moduleBiprodInl R _ M (moduleDiskCover R _ N) ≫
    moduleBiprodFst R _ M (moduleDiskCover R _ N) = 𝟙 M at h
  rw [h, E.functor.map_id, Category.id_comp, Iso.inv_hom_id]
  rfl
/-- 同じ切断と右脚の合成から、元の指定射を回収する。 -/
lemma dgBimoduleQuasiIsoSpanSection_right {P Q : BimoduleCategory R B C} (f : P ⟶ Q) :
    dgBimoduleQuasiIsoSpanSection R B C P Q ≫ dgBimoduleQuasiIsoSpanRight R B C f = f := by
  let E := rightModuleBimoduleEquivalence R B C
  change ((E.counitIso.app P).inv ≫ E.functor.map _) ≫
    E.functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanRight R _ (E.inverse.map f)) ≫ _ = _
  rw [Category.assoc, ← E.functor.map_comp_assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpan_inl_right]
  have h := E.counitIso.hom.naturality f
  change E.functor.map (E.inverse.map f) ≫ (E.counitIso.app Q).hom =
    (E.counitIso.app P).hom ≫ f at h
  rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
