module
public import SerrePositivity.DifferentialGraded.Bimodule.Right
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveResolution
public import SerrePositivity.DifferentialGraded.Derived.HomotopyComparison
public import SerrePositivity.DifferentialGraded.Derived.BimoduleBasic

/-! # 積dg圏上のsemifree bimodule解像度の比較

## 概要
積dg圏上のsemifree bimodule解像度の比較。

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
namespace SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution
open CategoryTheory Opposite
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]
variable {M : BimoduleCategory A B C}

/-- 増大射を既存の右加群圏へ戻し、既存射影解像度比較を使う。 -/
def toProjectiveResolution (P : BimoduleSemifreeResolution A B C M) :
    ModuleProjectiveResolution A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      ((rightModuleBimoduleEquivalence A B C).inverse.obj M) where
  obj := P.source
  π := (rightModuleBimoduleEquivalence A B C).functor.preimage
    (P.π ≫ ((rightModuleBimoduleEquivalence A B C).counitIso.app M).inv)
  projective := moduleSemifree_homotopicallyProjective A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ P.semifree
  quasiIso := (rightModuleBimoduleEquivalence_quasiIso_iff A B C _).1 (by
    rw [CategoryTheory.Functor.map_preimage]
    exact (BimoduleCategory.quasiIso A B C).comp_mem _ _ P.quasiIso
      ((BimoduleCategory.quasiIso A B C).of_isIso _))

lemma augmentation_fac (P : BimoduleSemifreeResolution A B C M) :
    (rightModuleBimoduleEquivalence A B C).functor.map P.toProjectiveResolution.π ≫
      ((rightModuleBimoduleEquivalence A B C).counitIso.app M).hom = P.π := by
  change (rightModuleBimoduleEquivalence A B C).functor.map
    ((rightModuleBimoduleEquivalence A B C).functor.preimage _) ≫ _ = _
  rw [CategoryTheory.Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]

def comparison (P Q : BimoduleSemifreeResolution A B C M) : P.obj ⟶ Q.obj :=
  (rightModuleBimoduleEquivalence A B C).functor.map
    (P.toProjectiveResolution.comparison Q.toProjectiveResolution)

lemma comparison_quasiIso (P Q : BimoduleSemifreeResolution A B C M) :
    BimoduleCategory.quasiIso A B C (P.comparison Q) :=
  (rightModuleBimoduleEquivalence_quasiIso_iff A B C _).2
    (P.toProjectiveResolution.comparison_quasiIso Q.toProjectiveResolution)

/-- 全dg自然な加群ホモトピーを、指定準同型の局所化で同一視する。 -/
lemma map_eq_of_source_homotopy
    {X Y : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ} (f g : X ⟶ Y)
    (h : (moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ).map f =
      (moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ).map g) :
    (bimoduleToDerived A B C).map ((rightModuleBimoduleEquivalence A B C).functor.map f) =
      (bimoduleToDerived A B C).map
        ((rightModuleBimoduleEquivalence A B C).functor.map g) := by
  apply moduleQuasiIso_equalizes_boundary A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    ((rightModuleBimoduleEquivalence A B C).functor ⋙ bimoduleToDerived A B C)
    (fun _ _ k hk => bimoduleToDerived_inverts A B C _
      ((rightModuleBimoduleEquivalence_quasiIso_iff A B C k).2 hk)) f g
  exact (moduleHomotopy_nonempty_iff A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ f g).1
    ((moduleToHomotopy_map_eq_iff A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ f g).1 h)

lemma comparison_fac (P Q : BimoduleSemifreeResolution A B C M) :
    (bimoduleToDerived A B C).map (P.comparison Q) ≫ (bimoduleToDerived A B C).map Q.π =
      (bimoduleToDerived A B C).map P.π := by
  have h := map_eq_of_source_homotopy
    (P.toProjectiveResolution.comparison Q.toProjectiveResolution ≫ Q.toProjectiveResolution.π)
    P.toProjectiveResolution.π
    (((moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ).map_comp _ _).trans
      (P.toProjectiveResolution.comparison_fac Q.toProjectiveResolution))
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  have hh := congrArg (fun k => k ≫ (bimoduleToDerived A B C).map
    ((rightModuleBimoduleEquivalence A B C).counitIso.app M).hom) h
  have haug (R : BimoduleSemifreeResolution A B C M) :
      (bimoduleToDerived A B C).map
          ((rightModuleBimoduleEquivalence A B C).functor.map R.toProjectiveResolution.π) ≫
        (bimoduleToDerived A B C).map
          ((rightModuleBimoduleEquivalence A B C).counitIso.app M).hom =
      (bimoduleToDerived A B C).map R.π :=
    ((bimoduleToDerived A B C).map_comp _ _).symm.trans
      (congrArg (bimoduleToDerived A B C).map R.augmentation_fac)
  rw [Category.assoc, haug Q, haug P] at hh
  exact hh

lemma comparison_unique (P Q : BimoduleSemifreeResolution A B C M) (s : P.obj ⟶ Q.obj)
    (hs : (bimoduleToDerived A B C).map s ≫ (bimoduleToDerived A B C).map Q.π =
      (bimoduleToDerived A B C).map P.π) :
    (bimoduleToDerived A B C).map (P.comparison Q) = (bimoduleToDerived A B C).map s := by
  apply (Iso.cancel_iso_hom_right _ _ (bimoduleDerivedIso A B C Q.π Q.quasiIso)).1
  exact (P.comparison_fac Q).trans hs.symm

def comparisonIso (P Q : BimoduleSemifreeResolution A B C M) :
    (bimoduleToDerived A B C).obj P.obj ≅ (bimoduleToDerived A B C).obj Q.obj :=
  bimoduleDerivedIso A B C (P.comparison Q) (P.comparison_quasiIso Q)

lemma comparisonIso_self (P : BimoduleSemifreeResolution A B C M) :
    P.comparisonIso P = Iso.refl _ := by
  apply Iso.ext
  have h := P.comparison_unique P (𝟙 P.obj) (by
    rw [CategoryTheory.Functor.map_id, Category.id_comp])
  exact h.trans ((bimoduleToDerived A B C).map_id _)

lemma comparisonIso_trans (P Q R : BimoduleSemifreeResolution A B C M) :
    P.comparisonIso Q ≪≫ Q.comparisonIso R = P.comparisonIso R := by
  apply Iso.ext
  apply (Iso.cancel_iso_hom_right _ _ (bimoduleDerivedIso A B C R.π R.quasiIso)).1
  change ((bimoduleToDerived A B C).map (P.comparison Q) ≫
      (bimoduleToDerived A B C).map (Q.comparison R)) ≫
        (bimoduleToDerived A B C).map R.π =
    (bimoduleToDerived A B C).map (P.comparison R) ≫ (bimoduleToDerived A B C).map R.π
  rw [Category.assoc, comparison_fac, comparison_fac, comparison_fac]

end SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution
