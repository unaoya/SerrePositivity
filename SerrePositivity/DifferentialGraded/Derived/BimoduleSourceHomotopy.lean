module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleSemifreeComparison

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
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
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
