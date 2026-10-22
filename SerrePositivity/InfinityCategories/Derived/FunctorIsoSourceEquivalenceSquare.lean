module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoTwoStepSquare
public import SerrePositivity.InfinityCategories.Derived.FunctorHomSquareTransport
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPrecompAlgebra
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoPrecompNaturalitySquare
/-!
概要：指定済みの cell 入出力比較を、その同じ値と任意射の四角形で照合する。
方針：同じ入力同値の指定逆・augmentation・元の全関手比較を保持する。
規約：原 kernel の平坦性を追加しない。使われ方：元の cell 模型比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
lemma functorIso_source_equivalence_square
    {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (e : QCatEquivalence X Y) {H0 H1 : Y ⟶ Z} {G0 G1 : X ⟶ Z}
    (a0 : FunctorIso (e.hom ≫ H0) G0) (a1 : FunctorIso (e.hom ≫ H1) G1)
    (d : FunctorHom H0 H1) (f : FunctorHom G0 G1)
    (ha : a0.hom ≫ f = functorHomPrecomp H0 H1 e.hom d ≫ a1.hom)
    (b0 : FunctorIso H0 (e.inv ≫ G0)) (b1 : FunctorIso H1 (e.inv ≫ G1))
    (hb0 : HEq b0 ((FunctorIso.postcomp e.invHomIso H0).symm ≪≫ a0.precomp e.inv))
    (hb1 : HEq b1 ((FunctorIso.postcomp e.invHomIso H1).symm ≪≫ a1.precomp e.inv)) :
    b0.hom ≫ functorHomPrecomp G0 G1 e.inv f = d ≫ b1.hom := by
  let u0 : FunctorIso ((𝟙 Y) ≫ H0) ((e.inv ≫ e.hom) ≫ H0) :=
    (FunctorIso.postcomp e.invHomIso H0).symm
  let u1 : FunctorIso ((𝟙 Y) ≫ H1) ((e.inv ≫ e.hom) ≫ H1) :=
    (FunctorIso.postcomp e.invHomIso H1).symm
  have hu : u0.hom ≫ functorHomPrecomp H0 H1 (e.inv ≫ e.hom) d =
      functorHomPrecomp H0 H1 (𝟙 Y) d ≫ u1.hom := by
    simpa only [u0, u1, ← F2.functorIso_postcomp_symm,
      functorIso_postcomp_hom_typed] using!
      functorHom_whisker_exchange_typed e.invHomIso.inv d
  have hp := functorHomPrecomp_iso_square_forward a0 a1
    (functorHomPrecomp H0 H1 e.hom d) f e.inv ha
  rw [functorHomPrecomp_precomp] at hp
  have hs := functorIso_trans_hom_square u0 u1 (a0.precomp e.inv) (a1.precomp e.inv)
    (functorHomPrecomp H0 H1 (𝟙 Y) d)
    (functorHomPrecomp H0 H1 (e.inv ≫ e.hom) d)
    (functorHomPrecomp G0 G1 e.inv f) hu hp
  have hb0' := functorIso_hom_heq_of_endpoint_heq b0
    (u0 ≪≫ a0.precomp e.inv) (Category.id_comp H0).symm rfl hb0
  have hb1' := functorIso_hom_heq_of_endpoint_heq b1
    (u1 ≪≫ a1.precomp e.inv) (Category.id_comp H1).symm rfl hb1
  exact functorHom_two_two_eq_of_heq _ _ _ _ _ _ _ _
    (Category.id_comp H0).symm rfl (Category.id_comp H1).symm rfl
    hb0' HEq.rfl (heq_of_eq (functorHom_precomp_id d)).symm hb1' hs
end SerrePositivity.InfinityCategories
