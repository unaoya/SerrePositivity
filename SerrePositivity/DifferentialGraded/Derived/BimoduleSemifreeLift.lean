module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleSemifreeComposeComparison
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveResolutionLift

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
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
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
