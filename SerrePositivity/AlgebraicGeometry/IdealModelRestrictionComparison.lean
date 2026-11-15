module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.Ideal.Maps

/-!
概要：制限射の全体切断でのイデアル模型を、元の開の切断環へ戻す。
方針：resLE_app_top と topIso の逆同型の合成則。
規約：係数移送の法則。射の平坦性は使わない。
使われ方：C03 の opensCone 上の局所模型を元のスキームへ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

/-- 制限射の全体切断の模型を、topIso で元の開の切断へ戻す。 -/
theorem ideal_model_resLE_top_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (L : Ideal Γ(U.toScheme, ⊤)) (K : Ideal Γ(X, V))
    (hL : L.map (f.resLE U V h).appTop.hom = K.map V.topIso.inv.hom) :
    (L.map U.topIso.hom.hom).map (f.appLE U V h).hom = K := by
  have heq := congrArg (fun M : Ideal Γ(V.toScheme, ⊤) ↦ M.map V.topIso.hom.hom) hL
  simpa only [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.resLE_app_top,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, CommRingCat.hom_id, Ideal.map_id]
    using heq

/-- 逆像と等しい開での appLE の模型を、実際の app の模型へ戻す。 -/
theorem ideal_model_appLE_of_eq_preimage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 = f ⁻¹ᵁ U.1)
    (L : Ideal Γ(Y, U.1)) (K : X.IdealSheafData)
    (heq : L.map (f.appLE U.1 V.1 e.le).hom = K.ideal V) :
    L.map (f.app U.1).hom = K.ideal ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩ := by
  rcases V with ⟨V, hV⟩
  dsimp only at e
  subst V
  simpa only [Scheme.Hom.appLE_eq_app] using heq

end SerrePositivity.AlgebraicGeometry
