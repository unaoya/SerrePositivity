module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Tensor.Compose
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Bimodule.Right
public import SerrePositivity.DifferentialGraded.Derived.Projective
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Tensor.Triple
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
public import SerrePositivity.DifferentialGraded.Tensor.Graded

/-!
# Derived.BimoduleTensor

## 概要
17 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## BimoduleComposeHomotopy（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleComposeHomotopy.lean） -/

/-! # 任意の前因子とのbimodule合成後にsourceホモトピーを同一視する

## 概要
任意の前因子とのbimodule合成後にsourceホモトピーを同一視する。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleComposeHomotopy
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E] (P : BimoduleCategory A B C)

/-- すべての準同型の保存を要求せず、標準cylinderの射影だけを反転して境界を同一視する。 -/
lemma composeAfter_equalizes_source_boundary
    {M N : ModuleCategory A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ) f g) :
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map
      ((rightModuleBimoduleEquivalence A C E).functor.map f)) =
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map
      ((rightModuleBimoduleEquivalence A C E).functor.map g)) := by
  let H := (rightModuleBimoduleEquivalence A C E).functor ⋙
    composeAfter A B C E P ⋙ bimoduleToDerived A B E
  let I := modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M
  let d := moduleCylinderDesc A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ f g h
  have : IsIso (H.map I.π) := bimoduleToDerived_inverts A B E _
    (composeAfter_sourcePrecylinderProjection_quasiIso A B C E P M)
  have hi : H.map I.i₀ = H.map I.i₁ := by
    apply (Iso.cancel_iso_hom_right _ _ (asIso (H.map I.π))).1
    change H.map I.i₀ ≫ H.map I.π = H.map I.i₁ ≫ H.map I.π
    exact (H.map_comp _ _).symm.trans
      ((congrArg H.map I.i₀_π).trans
        ((congrArg H.map I.i₁_π.symm).trans (H.map_comp _ _)))
  change H.map f = H.map g
  calc
    _ = H.map (I.i₀ ≫ d) := congrArg H.map (moduleCylinderDesc_i₀ A _ f g h).symm
    _ = H.map I.i₀ ≫ H.map d := H.map_comp _ _
    _ = H.map I.i₁ ≫ H.map d := congrArg (fun k => k ≫ H.map d) hi
    _ = H.map (I.i₁ ≫ d) := (H.map_comp _ _).symm
    _ = _ := congrArg H.map (moduleCylinderDesc_i₁ A _ f g h)

lemma composeAfter_map_eq_of_source_homotopy
    {M N : ModuleCategory A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ} (f g : M ⟶ N)
    (h : (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map f =
      (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map g) :
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map
      ((rightModuleBimoduleEquivalence A C E).functor.map f)) =
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map
      ((rightModuleBimoduleEquivalence A C E).functor.map g)) :=
  composeAfter_equalizes_source_boundary A B C E P f g
    ((moduleHomotopy_nonempty_iff A _ f g).1 ((moduleToHomotopy_map_eq_iff A _ f g).1 h))

/-- 任意の実際のbimodule射も、積dg圏表示でホモトピックなら合成後の導来圏で一致する。 -/
lemma composeAfter_map_eq_of_inverse_source_homotopy
    {Q Q' : BimoduleCategory A C E} (f g : Q ⟶ Q')
    (h : (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A C E).inverse.map f) =
      (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A C E).inverse.map g)) :
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map f) =
      (bimoduleToDerived A B E).map ((composeAfter A B C E P).map g) := by
  let J := rightModuleBimoduleEquivalence A C E
  let T := composeAfter A B C E P ⋙ bimoduleToDerived A B E
  have he := composeAfter_map_eq_of_source_homotopy A B C E P
    (J.inverse.map f) (J.inverse.map g) h
  have hf := congrArg T.map (J.counitIso.hom.naturality f)
  have hg := congrArg T.map (J.counitIso.hom.naturality g)
  simp only [CategoryTheory.Functor.map_comp] at hf hg
  change T.map f = T.map g
  apply (Iso.cancel_iso_hom_left (T.mapIso (J.counitIso.app Q)) _ _).1
  exact hf.symm.trans ((congrArg (fun k => k ≫ T.map (J.counitIso.app Q').hom) he).trans hg)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleComposeHomotopy

/-! ## BimoduleSemifreeComparison（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleSemifreeComparison.lean） -/

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
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleSemifreeComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end BimoduleSemifreeComparison

/-! ## BimoduleSemifreeComposeComparison（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleSemifreeComposeComparison.lean） -/

/-! # semifree解像度の比較増大squareを任意の前因子と合成した後の整合性

## 概要
semifree解像度の比較増大squareを任意の前因子と合成した後の整合性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleSemifreeComposeComparison
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution
open CategoryTheory BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]

/-- semifree比較の増大squareは、任意の前因子との合成後の導来圏でも可換。 -/
lemma composeAfter_comparison_fac (P : BimoduleCategory A B D) {Q : BimoduleCategory A D E}
    (R S : BimoduleSemifreeResolution A D E Q) :
    (bimoduleToDerived A B E).map ((composeAfter A B D E P).map (R.comparison S)) ≫
        (bimoduleToDerived A B E).map ((composeAfter A B D E P).map S.π) =
      (bimoduleToDerived A B E).map ((composeAfter A B D E P).map R.π) := by
  let J := rightModuleBimoduleEquivalence A D E
  let T := composeAfter A B D E P ⋙ bimoduleToDerived A B E
  have h := composeAfter_map_eq_of_source_homotopy A B D E P
    (R.toProjectiveResolution.comparison S.toProjectiveResolution ≫ S.toProjectiveResolution.π)
    R.toProjectiveResolution.π
    (((moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ).map_comp _ _).trans
      (R.toProjectiveResolution.comparison_fac S.toProjectiveResolution))
  change T.map (J.functor.map (_ ≫ _)) = T.map (J.functor.map _) at h
  rw [J.functor.map_comp, T.map_comp] at h
  have hh := congrArg (fun k => k ≫ T.map (J.counitIso.app Q).hom) h
  have haug (U : BimoduleSemifreeResolution A D E Q) :
      T.map (J.functor.map U.toProjectiveResolution.π) ≫ T.map (J.counitIso.app Q).hom =
        T.map U.π :=
    (T.map_comp _ _).symm.trans (congrArg T.map U.augmentation_fac)
  rw [Category.assoc, haug S, haug R] at hh
  exact hh

end SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution
end

end BimoduleSemifreeComposeComparison

/-! ## BimoduleSemifreeLift（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleSemifreeLift.lean） -/

/-! # 任意の二つのsemifree解像度間への射の持ち上げと合成後の増大square

## 概要
任意の二つのsemifree解像度間への射の持ち上げと合成後の増大square。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleSemifreeLift
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution
open CategoryTheory BimoduleTensor
variable (A : Type u) [CommRing A] (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  {M N : BimoduleCategory A D E}

/-- 既存の射影解像度の持ち上げを、積dg圏表示の同値で戻す。 -/
def lift (R : BimoduleSemifreeResolution A D E M) (S : BimoduleSemifreeResolution A D E N)
    (f : M ⟶ N) : R.obj ⟶ S.obj :=
  (rightModuleBimoduleEquivalence A D E).functor.map
    (R.toProjectiveResolution.lift S.toProjectiveResolution
      ((rightModuleBimoduleEquivalence A D E).inverse.map f))

/-- 持ち上げの増大squareは主導来圏で可換。 -/
lemma lift_fac (R : BimoduleSemifreeResolution A D E M)
    (S : BimoduleSemifreeResolution A D E N) (f : M ⟶ N) :
    (bimoduleToDerived A D E).map (R.lift A D E S f) ≫ (bimoduleToDerived A D E).map S.π =
      (bimoduleToDerived A D E).map R.π ≫ (bimoduleToDerived A D E).map f := by
  let J := rightModuleBimoduleEquivalence A D E
  let T := bimoduleToDerived A D E
  let K := moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
  have hs : K.map (R.toProjectiveResolution.lift S.toProjectiveResolution (J.inverse.map f) ≫
      S.toProjectiveResolution.π) = K.map (R.toProjectiveResolution.π ≫ J.inverse.map f) :=
    (K.map_comp _ _).trans
      ((R.toProjectiveResolution.lift_fac S.toProjectiveResolution (J.inverse.map f)).trans
        (K.map_comp _ _).symm)
  have he := map_eq_of_source_homotopy _ _ hs
  change T.map (J.functor.map (_ ≫ _)) = T.map (J.functor.map (_ ≫ _)) at he
  simp only [CategoryTheory.Functor.map_comp] at he
  have h := congrArg (fun k => k ≫ T.map (J.counitIso.app N).hom) he
  have haug (U : BimoduleSemifreeResolution A D E N) :
      T.map (J.functor.map U.toProjectiveResolution.π) ≫ T.map (J.counitIso.app N).hom =
        T.map U.π :=
    (T.map_comp _ _).symm.trans (congrArg T.map U.augmentation_fac)
  rw [Category.assoc, haug S] at h
  have hn := congrArg T.map (J.counitIso.hom.naturality f)
  simp only [CategoryTheory.Functor.map_comp] at hn
  change T.map (J.functor.map (J.inverse.map f)) ≫ T.map (J.counitIso.app N).hom =
    T.map (J.counitIso.app M).hom ≫ T.map f at hn
  rw [Category.assoc, hn, ← Category.assoc] at h
  have hR := congrArg T.map R.augmentation_fac
  rw [T.map_comp] at hR
  rw [hR] at h
  exact h

/-- 任意の前因子と合成しても、持ち上げの増大squareは導来可換。 -/
lemma composeAfter_lift_fac (B : Type v) [DGCategory A B] [Small.{u} B]
    (P : BimoduleCategory A B D) (R : BimoduleSemifreeResolution A D E M)
    (S : BimoduleSemifreeResolution A D E N) (f : M ⟶ N) :
    (bimoduleToDerived A B E).map ((composeAfter A B D E P).map (R.lift A D E S f)) ≫
        (bimoduleToDerived A B E).map ((composeAfter A B D E P).map S.π) =
      (bimoduleToDerived A B E).map ((composeAfter A B D E P).map R.π) ≫
        (bimoduleToDerived A B E).map ((composeAfter A B D E P).map f) := by
  let J := rightModuleBimoduleEquivalence A D E
  let T := composeAfter A B D E P ⋙ bimoduleToDerived A B E
  let K := moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
  have hs : K.map (R.toProjectiveResolution.lift S.toProjectiveResolution (J.inverse.map f) ≫
      S.toProjectiveResolution.π) = K.map (R.toProjectiveResolution.π ≫ J.inverse.map f) :=
    (K.map_comp _ _).trans
      ((R.toProjectiveResolution.lift_fac S.toProjectiveResolution (J.inverse.map f)).trans
        (K.map_comp _ _).symm)
  have he := composeAfter_map_eq_of_source_homotopy A B D E P _ _ hs
  change T.map (J.functor.map (_ ≫ _)) = T.map (J.functor.map (_ ≫ _)) at he
  rw [J.functor.map_comp, T.map_comp, J.functor.map_comp, T.map_comp] at he
  have h := congrArg (fun k => k ≫ T.map (J.counitIso.app N).hom) he
  have haug (U : BimoduleSemifreeResolution A D E N) :
      T.map (J.functor.map U.toProjectiveResolution.π) ≫ T.map (J.counitIso.app N).hom =
        T.map U.π :=
    (T.map_comp _ _).symm.trans (congrArg T.map U.augmentation_fac)
  rw [Category.assoc, haug S] at h
  have hn := congrArg T.map (J.counitIso.hom.naturality f)
  rw [T.map_comp, T.map_comp] at hn
  change T.map (J.functor.map (J.inverse.map f)) ≫ T.map (J.counitIso.app N).hom =
    T.map (J.counitIso.app M).hom ≫ T.map f at hn
  rw [Category.assoc, hn, ← Category.assoc] at h
  have hR := congrArg T.map R.augmentation_fac
  rw [T.map_comp] at hR
  rw [hR] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution
end

end BimoduleSemifreeLift

/-! ## BimoduleSourceHomotopy（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleSourceHomotopy.lean） -/

/-! # 実際のbimodule射の積dg圏表示でのホモトピーを主導来圏で同一視する

## 概要
実際のbimodule射の積dg圏表示でのホモトピーを主導来圏で同一視する。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleSourceHomotopy
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (E : Type w) [DGCategory A E] [Small.{u} E]

lemma bimoduleDerived_map_eq_of_inverse_source_homotopy
    {Q Q' : BimoduleCategory A C E} (f g : Q ⟶ Q')
    (h : (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A C E).inverse.map f) =
      (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A C E).inverse.map g)) :
    (bimoduleToDerived A C E).map f = (bimoduleToDerived A C E).map g := by
  let J := rightModuleBimoduleEquivalence A C E
  let T := bimoduleToDerived A C E
  have he := BimoduleSemifreeResolution.map_eq_of_source_homotopy
    (J.inverse.map f) (J.inverse.map g) h
  have hf := congrArg T.map (J.counitIso.hom.naturality f)
  have hg := congrArg T.map (J.counitIso.hom.naturality g)
  simp only [CategoryTheory.Functor.map_comp] at hf hg
  apply (Iso.cancel_iso_hom_left (T.mapIso (J.counitIso.app Q)) _ _).1
  exact hf.symm.trans ((congrArg (fun k => k ≫ T.map (J.counitIso.app Q').hom) he).trans hg)

end SerrePositivity.DifferentialGraded
end

end BimoduleSourceHomotopy

/-! ## BimoduleRestrictionProjective（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleRestrictionProjective.lean） -/

/-!
概要：積 dg 圏の生成 sphere の右制限から固定 bimodule 解像度の射影性を回収する。
方針：同じ実制限同型と semifree filtration の Hom tower を使う。
規約：元の解像度を別の右射影的解像度へ取り替えない。
使われ方：cell source 上の二つの固定 graph 解像度。
-/

@[expose] public section BimoduleRestrictionProjective
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma BimoduleSemifreeResolution.right_homotopicallyProjective_of_cells
    {M : BimoduleCategory A B C} (P : BimoduleSemifreeResolution A B C M)
    (hcell : ∀ (c : C) (x : (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) (n : ℤ),
      moduleHomotopicallyProjective A B
        ((tensorRightRestriction A B C c).obj
          (freeSphere A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ x n))) (c : C) :
    moduleHomotopicallyProjective A B ((BimoduleCategory.evaluation A B C c).obj P.obj) := by
  exact moduleHomotopicallyProjective_of_iso A B
    (rightModuleBimoduleRightRestrictionIso A B C P.source c).symm
    (moduleSemifree_restriction_homotopicallyProjective A B
      (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (tensorRightRestrictionInclusion A B C c)
      (hcell c) P.semifree)

end SerrePositivity.DifferentialGraded
end

end BimoduleRestrictionProjective

/-! ## BimoduleRightProjective（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleRightProjective.lean） -/

/-!
概要：相手側 Hom の K-projective 性から同じ semifree bimodule 解像度の右射影性。
方針：生成 sphere の制限を K-projective 係数の自由加群へ同型で比較する。
規約：K-flat 性だけを使う相対平坦性とは区別する。
使われ方：標準 cell source 上の固定 graph 解像度。
-/

@[expose] public section BimoduleRightProjective
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma restrictedFree_homotopicallyProjective
    (hC : ∀ x y : C, (homObject A C x y).IsKProjective)
    (b₀ : B) (c₀ c : C) (K : Complex A) [K.IsKProjective] :
    moduleHomotopicallyProjective A B
      ((tensorRightRestriction A B C c).obj
        ((freeAt (A := A) (D := (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
          (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C))).obj K)) := by
  let := hC c₀ c
  let := complexTensor_isKProjective A K (homObject A C c₀ c)
  exact moduleHomotopicallyProjective_of_iso A B (restrictedFreeIso A B C b₀ c₀ c K).symm
    (freeAt_homotopicallyProjective A B b₀ _)

lemma BimoduleSemifreeResolution.right_homotopicallyProjective
    (hC : ∀ x y : C, (homObject A C x y).IsKProjective)
    {M : BimoduleCategory A B C} (P : BimoduleSemifreeResolution A B C M) (c : C) :
    moduleHomotopicallyProjective A B ((BimoduleCategory.evaluation A B C c).obj P.obj) := by
  apply P.right_homotopicallyProjective_of_cells A B C
  intro c x n
  let := isKProjective_of_homComplex_acyclic A (complexSphere A n)
    (fun _ hN => complexSphereHom_acyclic A _ n hN)
  exact restrictedFree_homotopicallyProjective A B C hC x.unop.1.unop x.unop.2 c
    (complexSphere A n)

end SerrePositivity.DifferentialGraded
end

end BimoduleRightProjective

/-! ## BimoduleTensor（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleTensor.lean） -/

/-! # 固定した右相対K-flat因子との合成の局所化への降下

## 概要
固定した右相対K-flat因子との合成の局所化への降下。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleTensorMaps.lean。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleTensor
universe u v w z

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 後のbimodule Qを固定した合成関手。 -/
def composeWith (Q : BimoduleCategory A C E) :
    BimoduleCategory A B C ⥤ BimoduleCategory A B E :=
  ((𝟭 (BimoduleCategory A B C)).prod'
    ((Functor.const (BimoduleCategory A B C)).obj Q)) ⋙ composeFunctor A B C E

lemma composeWith_preserves_quasiIso (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    BimoduleCategory.quasiIso A B C ≤ (BimoduleCategory.quasiIso A B E).inverseImage
      (composeWith A B C E Q) :=
  fun _ _ f hf => composeMap_first_quasiIso A B C E Q hQ f hf

lemma composeWith_toDerived_inverts (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    (BimoduleCategory.quasiIso A B C).IsInvertedBy
      (composeWith A B C E Q ⋙ bimoduleToDerived A B E) :=
  fun _ _ f hf => bimoduleToDerived_inverts A B E _
    (composeMap_first_quasiIso A B C E Q hQ f hf)

/-- Qの右制限の相対K-flat性により、前の変数を実際の導来bimodule圏へ降ろす。 -/
def derivedComposeWith (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E :=
  bimoduleDerivedLift A B C (composeWith A B C E Q ⋙ bimoduleToDerived A B E)
    (composeWith_toDerived_inverts A B C E Q hQ)

lemma derivedComposeWith_fac (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    bimoduleToDerived A B C ⋙ derivedComposeWith A B C E Q hQ =
      composeWith A B C E Q ⋙ bimoduleToDerived A B E :=
  bimoduleDerivedLift_fac A B C _ _

instance derivedComposeWith_lifting (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    Localization.Lifting (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (composeWith A B C E Q ⋙ bimoduleToDerived A B E) (derivedComposeWith A B C E Q hQ) :=
  ⟨eqToIso (derivedComposeWith_fac A B C E Q hQ)⟩

/-- 局所化前の対象での合成の計算同型。 -/
def derivedComposeWithComputation (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (P : BimoduleCategory A B C) :
    (derivedComposeWith A B C E Q hQ).obj ((bimoduleToDerived A B C).obj P) ≅
      (bimoduleToDerived A B E).obj ((composeWith A B C E Q).obj P) :=
  (eqToIso (derivedComposeWith_fac A B C E Q hQ)).app P

lemma derivedComposeWith_unique (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (G : DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E)
    (hG : bimoduleToDerived A B C ⋙ G = composeWith A B C E Q ⋙ bimoduleToDerived A B E) :
    G = derivedComposeWith A B C E Q hQ :=
  bimoduleDerivedLift_unique A B C G _ (hG.trans (derivedComposeWith_fac A B C E Q hQ).symm)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleTensor

/-! ## BimoduleTensorMaps（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleTensorMaps.lean） -/

/-! # 固定因子の射による合成関手とその局所化の自然変換

## 概要
固定因子の射による合成関手とその局所化の自然変換。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleTensorAssociator.lean、Derived/
BimoduleTensorFunctor.lean、Derived/BimoduleTensorKFlatComparison.lean等。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleTensorMaps
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

def composeWithMap {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q') :
    composeWith A B C E Q ⟶ composeWith A B C E Q' where
  app P := composeMap A B C E (𝟙 P) g
  naturality {P P'} f := by
    have h₁ := composeMap_comp A B C E f (𝟙 P') (𝟙 Q) g
    have h₂ := composeMap_comp A B C E (𝟙 P) f g (𝟙 Q')
    simp only [Category.comp_id, Category.id_comp] at h₁ h₂
    exact h₁.symm.trans h₂

lemma composeWithMap_id (Q : BimoduleCategory A C E) :
    composeWithMap A B C E (𝟙 Q) = 𝟙 (composeWith A B C E Q) := by
  apply NatTrans.ext
  funext P
  exact composeMap_id A B C E P Q

lemma composeWithMap_comp {Q Q' Q'' : BimoduleCategory A C E} (g : Q ⟶ Q') (h : Q' ⟶ Q'') :
    composeWithMap A B C E (g ≫ h) = composeWithMap A B C E g ≫ composeWithMap A B C E h := by
  apply NatTrans.ext
  funext P
  change composeMap A B C E (𝟙 P) (g ≫ h) =
    composeMap A B C E (𝟙 P) g ≫ composeMap A B C E (𝟙 P) h
  have hh := composeMap_comp A B C E (𝟙 P) (𝟙 P) g h
  simpa only [Category.id_comp] using hh

/-- Qの射を、局所化の自然変換の普遍性によって降ろす。 -/
def derivedComposeWithMap {Q Q' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (g : Q ⟶ Q') : derivedComposeWith A B C E Q hQ ⟶ derivedComposeWith A B C E Q' hQ' :=
  Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (composeWith A B C E Q ⋙ bimoduleToDerived A B E)
    (composeWith A B C E Q' ⋙ bimoduleToDerived A B E)
    (derivedComposeWith A B C E Q hQ) (derivedComposeWith A B C E Q' hQ')
    (whiskerRight (composeWithMap A B C E g) (bimoduleToDerived A B E))

lemma derivedComposeWithMap_app {Q Q' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (g : Q ⟶ Q') (P : BimoduleCategory A B C) :
    (derivedComposeWithMap A B C E hQ hQ' g).app ((bimoduleToDerived A B C).obj P) =
      (derivedComposeWithComputation A B C E Q hQ P).hom ≫
        (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) g) ≫
          (derivedComposeWithComputation A B C E Q' hQ' P).inv :=
  Localization.liftNatTrans_app (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (composeWith A B C E Q ⋙ bimoduleToDerived A B E)
    (composeWith A B C E Q' ⋙ bimoduleToDerived A B E)
    (derivedComposeWith A B C E Q hQ) (derivedComposeWith A B C E Q' hQ')
    (whiskerRight (composeWithMap A B C E g) (bimoduleToDerived A B E)) P

lemma derivedComposeWithMap_id (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    derivedComposeWithMap A B C E hQ hQ (𝟙 Q) = 𝟙 (derivedComposeWith A B C E Q hQ) := by
  unfold derivedComposeWithMap
  rw [composeWithMap_id]
  have hid : whiskerRight (𝟙 (composeWith A B C E Q)) (bimoduleToDerived A B E) =
      𝟙 (composeWith A B C E Q ⋙ bimoduleToDerived A B E) := by
    apply NatTrans.ext
    funext P
    exact (bimoduleToDerived A B E).map_id ((composeWith A B C E Q).obj P)
  rw [hid]
  exact Localization.liftNatTrans_id _ _ _ _

lemma derivedComposeWithMap_comp {Q Q' Q'' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (hQ'' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q''))
    (g : Q ⟶ Q') (h : Q' ⟶ Q'') :
    derivedComposeWithMap A B C E hQ hQ'' (g ≫ h) =
      derivedComposeWithMap A B C E hQ hQ' g ≫ derivedComposeWithMap A B C E hQ' hQ'' h := by
  unfold derivedComposeWithMap
  rw [Localization.comp_liftNatTrans, composeWithMap_comp, whiskerRight_comp]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleTensorMaps

/-! ## BimoduleTensorUnit（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleTensorUnit.lean） -/

/-! # 対角bimoduleを固定した導来合成の右単位自然同型

## 概要
対角bimoduleを固定した導来合成の右単位自然同型。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleTensorEvaluation.lean。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleTensorUnit
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]
local notation "Δ" => BimoduleCategory.of A C C (Bimodule.diagonal A C)

/-- 元のbimodule単位比較を出力の局所化へ送った自然同型。 -/
def rightUnitLocalizedIso :
    composeWith A B C C Δ ⋙ bimoduleToDerived A B C ≅ bimoduleToDerived A B C :=
  isoWhiskerRight (rightUnitNatIso A B C) (bimoduleToDerived A B C) ≪≫
    Functor.leftUnitor (bimoduleToDerived A B C)

lemma rightUnitLocalizedIso_hom_app (P : BimoduleCategory A B C) :
    (rightUnitLocalizedIso A B C).hom.app P =
      (bimoduleToDerived A B C).map
        (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom := by
  change (bimoduleToDerived A B C).map
      (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- 対角因子は右相対K-flatなので、単位比較を導来圏全体の自然同型に降ろせる。 -/
def derivedRightUnitIso :
    derivedComposeWith A B C C Δ (Bimodule.diagonal_rightRelativeKFlat A C) ≅
      𝟭 (DerivedBimoduleCategory A B C) :=
  Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (composeWith A B C C Δ ⋙ bimoduleToDerived A B C) (bimoduleToDerived A B C)
    (derivedComposeWith A B C C Δ (Bimodule.diagonal_rightRelativeKFlat A C))
    (𝟭 (DerivedBimoduleCategory A B C)) (rightUnitLocalizedIso A B C)

lemma derivedRightUnitIso_hom_app (P : BimoduleCategory A B C) :
    (derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P) =
      (derivedComposeWithComputation A B C C Δ (Bimodule.diagonal_rightRelativeKFlat A C) P).hom ≫
        (bimoduleToDerived A B C).map
          (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom := by
  have h := Localization.liftNatTrans_app (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C)
    (composeWith A B C C Δ ⋙ bimoduleToDerived A B C) (bimoduleToDerived A B C)
    (derivedComposeWith A B C C Δ (Bimodule.diagonal_rightRelativeKFlat A C))
    (𝟭 (DerivedBimoduleCategory A B C)) (rightUnitLocalizedIso A B C).hom P
  change (derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P) =
    (derivedComposeWithComputation A B C C Δ (Bimodule.diagonal_rightRelativeKFlat A C) P).hom ≫
      (rightUnitLocalizedIso A B C).hom.app P ≫ 𝟙 _ at h
  rw [Category.comp_id, rightUnitLocalizedIso_hom_app] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleTensorUnit

/-! ## BimoduleTensorFunctor（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleTensorFunctor.lean） -/

/-! # 右相対K-flat因子に関する導来合成関手の関手性

## 概要
右相対K-flat因子に関する導来合成関手の関手性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleLocalization.lean、Derived/
RightKFlatComposition.lean。固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleTensorFunctor
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 元の全dg自然な閉零bimodule圏の右相対K-flat対象の充満部分圏。 -/
abbrev RightKFlatBimoduleCategory := ObjectProperty.FullSubcategory
  (fun Q : BimoduleCategory A C E =>
    Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))

/-- 前の変数は局所化済み、後の変数は右相対K-flatな実際のbimoduleとしての関手性。 -/
def derivedComposeWithFunctor : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) where
  obj Q := derivedComposeWith A B C E Q.obj Q.property
  map {Q Q'} g := derivedComposeWithMap A B C E Q.property Q'.property g.hom
  map_id Q := derivedComposeWithMap_id A B C E Q.obj Q.property
  map_comp {Q Q' Q''} g h :=
    derivedComposeWithMap_comp A B C E Q.property Q'.property Q''.property g.hom h.hom

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleTensorFunctor

/-! ## BimoduleTensorComparison（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleTensorComparison.lean） -/

/-! # 片側の射影的bimodule間の準同型による導来合成関手の比較

## 概要
片側の射影的bimodule間の準同型による導来合成関手の比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleTensorComparison
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
variable {Q Q' : BimoduleCategory A C E}

/-- 各右制限が射影的な因子間の準同型は、局所化に値を持つ合成関手の同型を与える。 -/
def composeWithProjectiveIso
    (hQ : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q))
    (hQ' : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q'))
    (g : Q ⟶ Q') (hg : BimoduleCategory.quasiIso A C E g) :
    composeWith A B C E Q ⋙ bimoduleToDerived A B E ≅
      composeWith A B C E Q' ⋙ bimoduleToDerived A B E := by
  let a := whiskerRight (composeWithMap A B C E g) (bimoduleToDerived A B E)
  haveI : ∀ P, IsIso (a.app P) := fun P => bimoduleToDerived_inverts A B E _
    (composeMap_second_projective_quasiIso A B C E P hQ hQ' g hg)
  haveI : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a

@[simp]
lemma composeWithProjectiveIso_hom (hQ hQ' g hg) :
    (composeWithProjectiveIso A B C E (Q := Q) (Q' := Q') hQ hQ' g hg).hom =
      whiskerRight (composeWithMap A B C E g) (bimoduleToDerived A B E) := rfl

/-- 実際の導来圏を始域とする、同じ準同型による合成関手の比較自然同型。 -/
def derivedComposeWithProjectiveIso
    (hF : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hF' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (hQ : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q))
    (hQ' : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q'))
    (g : Q ⟶ Q') (hg : BimoduleCategory.quasiIso A C E g) :
    derivedComposeWith A B C E Q hF ≅ derivedComposeWith A B C E Q' hF' :=
  Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (composeWith A B C E Q ⋙ bimoduleToDerived A B E)
    (composeWith A B C E Q' ⋙ bimoduleToDerived A B E)
    (derivedComposeWith A B C E Q hF) (derivedComposeWith A B C E Q' hF')
    (composeWithProjectiveIso A B C E hQ hQ' g hg)

@[simp]
lemma derivedComposeWithProjectiveIso_hom (hF hF' hQ hQ' g hg) :
    (derivedComposeWithProjectiveIso A B C E (Q := Q) (Q' := Q') hF hF' hQ hQ' g hg).hom =
      derivedComposeWithMap A B C E hF hF' g := rfl

lemma derivedComposeWithProjectiveIso_id
    (hF : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q)) :
    derivedComposeWithProjectiveIso A B C E hF hF hQ hQ (𝟙 Q)
      ((BimoduleCategory.quasiIso A C E).id_mem Q) = Iso.refl _ := by
  apply Iso.ext
  rw [derivedComposeWithProjectiveIso_hom, derivedComposeWithMap_id]
  rfl

lemma derivedComposeWithProjectiveIso_trans {Q'' : BimoduleCategory A C E}
    (hF : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hF' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (hF'' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q''))
    (hQ : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q))
    (hQ' : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q'))
    (hQ'' : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q''))
    (g : Q ⟶ Q') (h : Q' ⟶ Q'')
    (hg : BimoduleCategory.quasiIso A C E g) (hh : BimoduleCategory.quasiIso A C E h) :
    derivedComposeWithProjectiveIso A B C E hF hF' hQ hQ' g hg ≪≫
      derivedComposeWithProjectiveIso A B C E hF' hF'' hQ' hQ'' h hh =
    derivedComposeWithProjectiveIso A B C E hF hF'' hQ hQ'' (g ≫ h)
      ((BimoduleCategory.quasiIso A C E).comp_mem g h hg hh) := by
  apply Iso.ext
  simp only [Iso.trans_hom, derivedComposeWithProjectiveIso_hom]
  exact (derivedComposeWithMap_comp A B C E hF hF' hF'' g h).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleTensorComparison

/-! ## BimoduleTensorAssociator（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleTensorAssociator.lean） -/

/-! # 固定した右相対K-flat二因子に関する導来合成の結合比較

## 概要
固定した右相対K-flat二因子に関する導来合成の結合比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleTensorEvaluation.lean。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleTensorAssociator
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)

/-- 元の閉零合成関手の、前のbimodule変数に自然な結合比較。 -/
def composeWithAssociatorIso :
    composeWith A B C E Q ⋙ composeWith A B E F R ≅ composeWith A B C F (BimoduleCategory.of A C F
      (compose A C E F
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R))) :=
  NatIso.ofComponents
    (fun P => associatorIso A B C E F (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R))
    (fun f => by
      have h := associatorIso_naturality A B C E F f (𝟙 Q) (𝟙 R)
      rw [composeMap_id] at h
      exact h)

@[simp]
lemma composeWithAssociatorIso_app (P : BimoduleCategory A B C) :
    (composeWithAssociatorIso A B C E F Q R).app P =
      associatorIso A B C E F (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A
      C E Q) (BimoduleCategory.underlying A E F R) := rfl

variable (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
  (hR : Bimodule.rightRelativeKFlat A E F (BimoduleCategory.underlying A E F R))
include hQ hR

lemma derivedComposeWithPair_fac :
    bimoduleToDerived A B C ⋙
        (derivedComposeWith A B C E Q hQ ⋙ derivedComposeWith A B E F R hR) =
      (composeWith A B C E Q ⋙ composeWith A B E F R) ⋙ bimoduleToDerived A B F := by
  rfl

instance derivedComposeWithPair_lifting :
    Localization.Lifting (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      ((composeWith A B C E Q ⋙ composeWith A B E F R) ⋙ bimoduleToDerived A B F)
      (derivedComposeWith A B C E Q hQ ⋙ derivedComposeWith A B E F R hR) :=
  ⟨eqToIso (derivedComposeWithPair_fac A B C E F Q R hQ hR)⟩

/-- 右相対K-flat性の合成閉性を使った、実際の導来圏上の結合自然同型。 -/
def derivedAssociatorIso :
    derivedComposeWith A B C E Q hQ ⋙ derivedComposeWith A B E F R hR ≅
      derivedComposeWith A B C F (BimoduleCategory.of A C F (compose A C E F
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)))
      (Bimodule.rightRelativeKFlat_compose A C E F (BimoduleCategory.underlying A C E Q)
      (BimoduleCategory.underlying A E F R) hQ hR) :=
  Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    ((composeWith A B C E Q ⋙ composeWith A B E F R) ⋙ bimoduleToDerived A B F)
    (composeWith A B C F (BimoduleCategory.of A C F (compose A C E F
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R))) ⋙
      bimoduleToDerived A B F)
    (derivedComposeWith A B C E Q hQ ⋙ derivedComposeWith A B E F R hR)
    (derivedComposeWith A B C F (BimoduleCategory.of A C F (compose A C E F
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)))
      (Bimodule.rightRelativeKFlat_compose A C E F (BimoduleCategory.underlying A C E Q)
      (BimoduleCategory.underlying A E F R) hQ hR))
    (isoWhiskerRight (composeWithAssociatorIso A B C E F Q R) (bimoduleToDerived A B F))

lemma derivedAssociatorIso_hom_app (P : BimoduleCategory A B C) :
    (derivedAssociatorIso A B C E F Q R hQ hR).hom.app ((bimoduleToDerived A B C).obj P) =
      (eqToIso (derivedComposeWithPair_fac A B C E F Q R hQ hR)).hom.app P ≫
        (bimoduleToDerived A B F).map
          (associatorIso A B C E F (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)).hom ≫
        (derivedComposeWithComputation A B C F (BimoduleCategory.of A C F (compose A C E F
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)))
          (Bimodule.rightRelativeKFlat_compose A C E F (BimoduleCategory.underlying A C E Q)
      (BimoduleCategory.underlying A E F R) hQ hR) P).inv :=
  Localization.liftNatTrans_app (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    ((composeWith A B C E Q ⋙ composeWith A B E F R) ⋙ bimoduleToDerived A B F)
    (composeWith A B C F (BimoduleCategory.of A C F (compose A C E F
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R))) ⋙
      bimoduleToDerived A B F)
    (derivedComposeWith A B C E Q hQ ⋙ derivedComposeWith A B E F R hR)
    (derivedComposeWith A B C F (BimoduleCategory.of A C F (compose A C E F
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)))
      (Bimodule.rightRelativeKFlat_compose A C E F (BimoduleCategory.underlying A C E Q)
      (BimoduleCategory.underlying A E F R) hQ hR))
    (isoWhiskerRight (composeWithAssociatorIso A B C E F Q R) (bimoduleToDerived A B F)).hom P

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleTensorAssociator

/-! ## BimoduleTensorEvaluation（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleTensorEvaluation.lean） -/

/-! # 標準局所化の元の対象・射上での導来合成の計算

## 概要
標準局所化の元の対象・射上での導来合成の計算。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionRightUnit.lean、Derived/
BimoduleCompositionValueNaturality.lean、Derived/BimoduleTensorNaturality.lean等。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleTensorEvaluation
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma derivedComposeWith_map_base (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    {P P' : BimoduleCategory A B C} (f : P ⟶ P') :
    (derivedComposeWith A B C E Q hQ).map ((bimoduleToDerived A B C).map f) =
      (bimoduleToDerived A B E).map (composeMap A B C E f (𝟙 Q)) := rfl

lemma derivedComposeWithMap_base_app {Q Q' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (g : Q ⟶ Q') (P : BimoduleCategory A B C) :
    (derivedComposeWithMap A B C E hQ hQ' g).app ((bimoduleToDerived A B C).obj P) =
      (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) g) := by
  have h := derivedComposeWithMap_app A B C E hQ hQ' g P
  change (derivedComposeWithMap A B C E hQ hQ' g).app ((bimoduleToDerived A B C).obj P) =
    𝟙 _ ≫ (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) g) ≫ 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h

lemma derivedRightUnitIso_base_app (P : BimoduleCategory A B C) :
    (derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P) =
      (bimoduleToDerived A B C).map
        (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom := by
  have h := derivedRightUnitIso_hom_app A B C P
  change (derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P) =
    𝟙 _ ≫ (bimoduleToDerived A B C).map
      (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom at h
  exact h.trans (Category.id_comp _)

variable (F : Type t) [DGCategory A F] [Small.{u} E]

lemma derivedAssociatorIso_base_app (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hR : Bimodule.rightRelativeKFlat A E F (BimoduleCategory.underlying A E F R))
    (P : BimoduleCategory A B C) :
    (derivedAssociatorIso A B C E F Q R hQ hR).hom.app ((bimoduleToDerived A B C).obj P) =
      (bimoduleToDerived A B F).map
        (associatorIso A B C E F (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)).hom := by
  have h := derivedAssociatorIso_hom_app A B C E F Q R hQ hR P
  change (derivedAssociatorIso A B C E F Q R hQ hR).hom.app
      ((bimoduleToDerived A B C).obj P) = 𝟙 _ ≫ (bimoduleToDerived A B F).map
        (associatorIso A B C E F (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)).hom ≫ 𝟙 _
      at h
  simpa only [Category.id_comp, Category.comp_id] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleTensorEvaluation

/-! ## BimoduleTensorTriangle（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleTensorTriangle.lean） -/

/-! # 固定した右相対K-flat因子に関する導来合成の三角coherence

## 概要
固定した右相対K-flat因子に関する導来合成の三角coherence。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionTriangle.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleTensorTriangle
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma derivedTriangle (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    (derivedAssociatorIso A B C C E
        (BimoduleCategory.of A C C (Bimodule.diagonal A C)) Q
        (Bimodule.diagonal_rightRelativeKFlat A C) hQ).hom ≫
      derivedComposeWithMap A B C E
        (Bimodule.rightRelativeKFlat_compose A C C E (Bimodule.diagonal A C)
          (BimoduleCategory.underlying A C E Q) (Bimodule.diagonal_rightRelativeKFlat A C) hQ)
        hQ (leftBimoduleUnitIso A C E (BimoduleCategory.underlying A C E Q)).hom =
    whiskerRight (derivedRightUnitIso A B C).hom (derivedComposeWith A B C E Q hQ) ≫
      (Functor.leftUnitor (derivedComposeWith A B C E Q hQ)).hom := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app, whiskerRight_app, Functor.leftUnitor_hom_app,
    derivedAssociatorIso_base_app, derivedComposeWithMap_base_app,
    derivedRightUnitIso_base_app, derivedComposeWith_map_base]
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun f => (bimoduleToDerived A B E).map f)
    (triangle A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleTensorTriangle

/-! ## BimoduleTensorNaturality（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleTensorNaturality.lean） -/

/-! # 固定因子の二つの射に関する導来結合比較の自然性

## 概要
固定因子の二つの射に関する導来結合比較の自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionAssociatorNaturality.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleTensorNaturality
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

lemma derivedAssociatorIso_naturality {Q Q' : BimoduleCategory A C E}
    {R R' : BimoduleCategory A E F}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (hR : Bimodule.rightRelativeKFlat A E F (BimoduleCategory.underlying A E F R))
    (hR' : Bimodule.rightRelativeKFlat A E F (BimoduleCategory.underlying A E F R'))
    (g : Q ⟶ Q') (h : R ⟶ R') :
    (whiskerRight (derivedComposeWithMap A B C E hQ hQ' g) (derivedComposeWith A B E F R hR) ≫
        whiskerLeft (derivedComposeWith A B C E Q' hQ')
          (derivedComposeWithMap A B E F hR hR' h)) ≫
      (derivedAssociatorIso A B C E F Q' R' hQ' hR').hom =
    (derivedAssociatorIso A B C E F Q R hQ hR).hom ≫
      derivedComposeWithMap A B C F
        (Bimodule.rightRelativeKFlat_compose A C E F
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R) hQ hR)
        (Bimodule.rightRelativeKFlat_compose A C E F
          (BimoduleCategory.underlying A C E Q') (BimoduleCategory.underlying A E F R') hQ' hR')
        (composeMap A C E F g h) := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    derivedComposeWithMap_base_app, derivedComposeWith_map_base, derivedAssociatorIso_base_app]
  have hm : (derivedComposeWithMap A B E F hR hR' h).app
      ((derivedComposeWith A B C E Q' hQ').obj ((bimoduleToDerived A B C).obj P)) =
      (bimoduleToDerived A B F).map (composeMap A B E F
        (𝟙 (BimoduleCategory.of A B E (compose A B C E
          (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q')))) h) :=
    derivedComposeWithMap_base_app A B E F hR hR' h
      (BimoduleCategory.of A B E (compose A B C E
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q')))
  rw [hm]
  simp only [← CategoryTheory.Functor.map_comp]
  have hc := composeMap_comp A B E F (composeMap A B C E (𝟙 P) g)
    (𝟙 (BimoduleCategory.of A B E (compose A B C E
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q')))) (𝟙 R) h
  simp only [Category.comp_id, Category.id_comp] at hc
  have hn := associatorIso_naturality A B C E F (𝟙 P) g h
  rw [hc] at hn
  exact congrArg (fun f => (bimoduleToDerived A B F).map f) hn

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleTensorNaturality

/-! ## BimoduleTensorKFlatComparison（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleTensorKFlatComparison.lean） -/

/-! # 右相対K-flat因子間の準同型による導来合成の比較

## 概要
右相対K-flat因子間の準同型による導来合成の比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleLocalization.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleTensorKFlatComparison
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
variable {Q Q' : BimoduleCategory A C E}

def composeWithKFlatIso
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (g : Q ⟶ Q') (hg : BimoduleCategory.quasiIso A C E g) :
    composeWith A B C E Q ⋙ bimoduleToDerived A B E ≅
      composeWith A B C E Q' ⋙ bimoduleToDerived A B E := by
  let a := whiskerRight (composeWithMap A B C E g) (bimoduleToDerived A B E)
  haveI : ∀ P, IsIso (a.app P) := fun P => bimoduleToDerived_inverts A B E _
    (composeMap_second_kFlat_quasiIso A B C E P hQ hQ' g hg)
  haveI : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a

@[simp]
lemma composeWithKFlatIso_hom (hQ hQ' g hg) :
    (composeWithKFlatIso A B C E (Q := Q) (Q' := Q') hQ hQ' g hg).hom =
      whiskerRight (composeWithMap A B C E g) (bimoduleToDerived A B E) := rfl

def derivedComposeWithKFlatIso
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (g : Q ⟶ Q') (hg : BimoduleCategory.quasiIso A C E g) :
    derivedComposeWith A B C E Q hQ ≅ derivedComposeWith A B C E Q' hQ' :=
  Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (composeWith A B C E Q ⋙ bimoduleToDerived A B E)
    (composeWith A B C E Q' ⋙ bimoduleToDerived A B E)
    (derivedComposeWith A B C E Q hQ) (derivedComposeWith A B C E Q' hQ')
    (composeWithKFlatIso A B C E hQ hQ' g hg)

@[simp]
lemma derivedComposeWithKFlatIso_hom (hQ hQ' g hg) :
    (derivedComposeWithKFlatIso A B C E (Q := Q) (Q' := Q') hQ hQ' g hg).hom =
      derivedComposeWithMap A B C E hQ hQ' g := rfl

lemma derivedComposeWithKFlatIso_id
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    derivedComposeWithKFlatIso A B C E hQ hQ (𝟙 Q)
      ((BimoduleCategory.quasiIso A C E).id_mem Q) = Iso.refl _ := by
  apply Iso.ext
  rw [derivedComposeWithKFlatIso_hom, derivedComposeWithMap_id]
  rfl

lemma derivedComposeWithKFlatIso_trans {Q'' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (hQ'' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q''))
    (g : Q ⟶ Q') (h : Q' ⟶ Q'')
    (hg : BimoduleCategory.quasiIso A C E g) (hh : BimoduleCategory.quasiIso A C E h) :
    derivedComposeWithKFlatIso A B C E hQ hQ' g hg ≪≫
      derivedComposeWithKFlatIso A B C E hQ' hQ'' h hh =
    derivedComposeWithKFlatIso A B C E hQ hQ'' (g ≫ h)
      ((BimoduleCategory.quasiIso A C E).comp_mem g h hg hh) := by
  apply Iso.ext
  simp only [Iso.trans_hom, derivedComposeWithKFlatIso_hom]
  exact (derivedComposeWithMap_comp A B C E hQ hQ' hQ'' g h).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleTensorKFlatComparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.4.3.14" (partial := special) "仮定：通常のモノイダル圏に必要な余等化子があり左右のテンソルがそれを保つ。または小さい dg 圏と後二つが右相対 K-flat な dg 双加群（Lean が強い：通常圏、または指定した K-flat な dg 双加群）。結論：相対テンソルの二つの括り方を結ぶ同型を構成し、通常の導来圏の版では第一変数に関して自然な同型を得る（この仮定での HA の結論の一部に一致）。一般の ∞ 双加群圏は含まれない。"] _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.derivedAssociatorIso
