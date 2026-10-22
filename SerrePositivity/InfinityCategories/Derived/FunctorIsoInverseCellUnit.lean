module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoInverseSourceComparison
/-!
概要：前向きの二つの単位正方形を指定逆に沿う cell 単位正方形へ移す。
方針：同じ共通 graph 比較の相殺と h Fun の実交換則を使う。
規約：同値の三角式は仮定しない。使われ方：元の diagonal cell 比較の単位。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorIso_inverse_cell_unit {A X : SSet.{u}} [Quasicategory X]
    (h : A ⟶ X) (s : X ⟶ A) (d : FunctorIso (s ≫ h) (𝟙 X))
    (F : X ⟶ X) (G : A ⟶ A) (T : A ⟶ X)
    (a : FunctorIso (h ≫ F) T) (b : FunctorIso (G ≫ h) T) (v : FunctorIso T h)
    (uF : FunctorIso F (𝟙 X)) (uG : FunctorIso G (𝟙 A))
    (ha : a ≪≫ v = uF.precomp h) (hb : b ≪≫ v = uG.postcomp h) :
    (FunctorIso.postcomp d.symm F ≪≫ a.precomp s ≪≫ FunctorIso.precomp b.symm s) ≪≫
      (uG.postcomp h).precomp s = uF ≪≫ d.symm := by
  have hc : a ≪≫ b.symm ≪≫ uG.postcomp h = uF.precomp h := by
    rw [← hb]
    simpa only [Iso.symm_self_id_assoc] using ha
  calc
    _ = FunctorIso.postcomp d.symm F ≪≫
        FunctorIso.precomp (f := h ≫ F) (g := h)
          (a ≪≫ b.symm ≪≫ uG.postcomp h) s := by
      simp only [F2.functorIso_precomp_trans, Iso.trans_assoc]
    _ = FunctorIso.postcomp d.symm F ≪≫ (uF.precomp h).precomp s := by rw [hc]
    _ = _ := by
      have hx := F2.functorIso_whisker_exchange d.symm uF
      simpa only [F2.functorIso_precomp_precomp, functorIso_precomp_id,
        F2.functorIso_postcomp_id] using! hx
end
end SerrePositivity.InfinityCategories
