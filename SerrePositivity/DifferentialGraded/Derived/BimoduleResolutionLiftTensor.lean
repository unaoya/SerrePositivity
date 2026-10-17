module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleResolutionLift
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposeHomotopy

/-! # 任意の準同型への標準解像度の持ち上げと相対tensor後の増大square

## 概要
任意の準同型への標準解像度の持ち上げと相対tensor後の増大square。

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
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E] (P : BimoduleCategory A B C)

/-- 任意の前因子と合成した後も、標準解像度の持ち上げの増大三角形は導来可換。 -/
lemma composeAfter_bimoduleCanonicalResolutionLift_fac {M N : BimoduleCategory A C E}
    (q : N ⟶ M) (hq : BimoduleCategory.quasiIso A C E q) :
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map
        (bimoduleCanonicalResolutionLift A C E q hq)) ≫
      (bimoduleToDerived A B E).map ((composeAfter A B C E P).map q) =
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map
      (bimoduleCanonicalSemifreeResolution A C E M).π) := by
  let H := rightModuleBimoduleEquivalence A C E
  let R := bimoduleSourceProjectiveResolution A C E M
  let T := composeAfter A B C E P ⋙ bimoduleToDerived A B E
  have hs := Classical.choose_spec (moduleHomotopicallyProjective_homotopy_lift
    A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ R.projective (H.inverse.map q)
    ((rightModuleBimodule_inverse_quasiIso_iff A C E q).2 hq) R.π)
  have hsK : (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map
      (bimoduleCanonicalResolutionSourceLift A C E q hq ≫ H.inverse.map q) =
    (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map R.π :=
    (moduleToHomotopy_map_eq_iff A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ _ _).2 hs
  have he := composeAfter_map_eq_of_source_homotopy A B C E P _ _ hsK
  change T.map (H.functor.map _) = T.map (H.functor.map _) at he
  have hl : H.functor.map
      (bimoduleCanonicalResolutionSourceLift A C E q hq ≫ H.inverse.map q) ≫
      (H.counitIso.app M).hom = bimoduleCanonicalResolutionLift A C E q hq ≫ q := by
    change H.functor.map (_ ≫ _) ≫ (H.counitIso.app M).hom =
      (H.functor.map _ ≫ (H.counitIso.app N).hom) ≫ q
    rw [H.functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (fun k => H.functor.map
      (bimoduleCanonicalResolutionSourceLift A C E q hq) ≫ k) (H.counitIso.hom.naturality q)
  have hh := congrArg (fun k => k ≫ T.map (H.counitIso.app M).hom) he
  rw [← T.map_comp, hl, ← T.map_comp] at hh
  exact (T.map_comp _ _).symm.trans hh

end SerrePositivity.DifferentialGraded.BimoduleTensor
