module
public import SerrePositivity.InfinityCategories.Core.FunctorIsoWhiskerAlgebra
/-!
概要：指定済みの canonical cell 模型比較を、同じ増大上の別模型の比較へ接続する。
方針：元の出力比較の式を代入し、同じ cell 始域の指定逆で前合成する。
規約：元の比較・指定逆を変更しない。使われ方：一般 cell 模型の選択整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
lemma functorIso_model_comparison_transfer {X Y Z : SSet.{w}}
    (s : X ⟶ Y) {K : X ⟶ Z} {A B0 B1 : Y ⟶ Z}
    (c : FunctorIso K (s ≫ A)) (a0 : FunctorIso B0 A) (a1 : FunctorIso B1 A)
    (e : FunctorIso B0 B1) (he : e = a0 ≪≫ a1.symm) :
    (c ≪≫ FunctorIso.precomp a0.symm s) ≪≫ FunctorIso.precomp e s =
      c ≪≫ FunctorIso.precomp a1.symm s := by
  rw [he, F2.functorIso_precomp_trans]
  simp only [F2.functorIso_precomp_symm, Iso.trans_assoc, Iso.symm_self_id_assoc]
end SerrePositivity.InfinityCategories
