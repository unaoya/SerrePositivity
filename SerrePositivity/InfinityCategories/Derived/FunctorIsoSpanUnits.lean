module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoWhiskerSpan
/-!
概要：実 tensor span の κ 正方形と通常単位子を同じ span 単位へ接続する。
方針：比較の結合と同じ前後合成を圏一般で先に計算する。
規約：実比較の値を変えない。使われ方：canonical cell tensor 単位の値の照合。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorIso_post_span_unit {X Z : SSet.{u}} (F0 F1 Fmid : X ⟶ X) (H : X ⟶ Z)
    {T0 T1 T2 : X ⟶ Z} (a0 : FunctorIso Fmid F0) (a1 : FunctorIso Fmid F1)
    (b0 : FunctorIso T2 T0) (b1 : FunctorIso T2 T1)
    (k0 : FunctorIso (F0 ≫ H) T0) (k1 : FunctorIso (F1 ≫ H) T1)
    (u : FunctorIso F1 (𝟙 X)) (v : FunctorIso T1 H)
    (hs : k0 ≪≫ b0.symm ≪≫ b1 =
      FunctorIso.postcomp a0.symm H ≪≫ a1.postcomp H ≪≫ k1)
    (hu : k1 ≪≫ v = u.postcomp H) :
    k0 ≪≫ b0.symm ≪≫ b1 ≪≫ v =
      FunctorIso.postcomp (f := F0) (g := 𝟙 X) ((a0.symm ≪≫ a1) ≪≫ u) H := by
  have ht := congrArg (fun z ↦ z ≪≫ v) hs
  simpa only [F2.functorIso_postcomp_trans, F2.functorIso_postcomp_symm,
    Iso.trans_assoc, hu] using! ht
lemma functorIso_pre_span_unit {X Y : SSet.{u}} (H : X ⟶ Y) (F0 F1 Fmid : Y ⟶ Y)
    {T0 T1 T2 : X ⟶ Y} (a0 : FunctorIso Fmid F0) (a1 : FunctorIso Fmid F1)
    (b0 : FunctorIso T2 T0) (b1 : FunctorIso T2 T1)
    (k0 : FunctorIso (H ≫ F0) T0) (k1 : FunctorIso (H ≫ F1) T1)
    (u : FunctorIso F1 (𝟙 Y)) (v : FunctorIso T1 H)
    (hs : k0 ≪≫ b0.symm ≪≫ b1 =
      FunctorIso.precomp a0.symm H ≪≫ a1.precomp H ≪≫ k1)
    (hu : k1 ≪≫ v = u.precomp H) :
    k0 ≪≫ b0.symm ≪≫ b1 ≪≫ v =
      FunctorIso.precomp (f := F0) (g := 𝟙 Y) ((a0.symm ≪≫ a1) ≪≫ u) H := by
  have ht := congrArg (fun z ↦ z ≪≫ v) hs
  simpa only [F2.functorIso_precomp_trans, F2.functorIso_precomp_symm,
    Iso.trans_assoc, hu] using! ht
end
end SerrePositivity.InfinityCategories
