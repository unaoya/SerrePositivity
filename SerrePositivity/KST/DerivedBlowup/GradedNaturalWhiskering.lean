module

public import SerrePositivity.DifferentialGraded.Module.RestrictionEnriched

/-!
概要：KST §3.1 の canonical な cartesian 比較を作るための全次数自然変換の whiskering。
方針：既存 GradedNatTrans と dg 関手の Hom 写像・積保存を使う。
規約：通常の閉零自然性だけに置き換えず、パラメータ複体に関する全次数自然性を保持する。
使われ方：係数図式の単位矢を実際の dg 加群比較へ送る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory
open DifferentialGraded

variable {R : Type u} [CommRing R]
  {C : Type v} {D : Type w} {E : Type t} [DGCategory R C] [DGCategory R D] [DGCategory R E]
  {K : Complex R}

/-- 概要：全次数自然変換を dg 関手で後合成する。
方針：各成分を Hom 写像で送り、dg 関手の積保存で元の自然性へ帰着する。
規約：KST §3.1。使われ方：係数圏の単位矢を図式加群の Hom へ送る。 -/
def dgGradedWhiskerRight {F G : DGFunctor R C D}
    (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) F G) (H : DGFunctor R D E) :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj K)
      (F.comp H) (G.comp H) where
  app x := τ.app x ≫ H.map (F.obj x) (G.obj x)
  naturality x y := by
    change (β_ K (x ⟶[Complex R] y)).hom ≫
      ((F.map x y ≫ H.map (F.obj x) (F.obj y)) ⊗ₘ
        (τ.app y ≫ H.map (F.obj y) (G.obj y))) ≫
        eComp (Complex R) _ _ _ =
      ((τ.app x ≫ H.map (F.obj x) (G.obj x)) ⊗ₘ
        (G.map x y ≫ H.map (G.obj x) (G.obj y))) ≫ eComp (Complex R) _ _ _
    rw [← tensorHom_comp_tensorHom_assoc, ← H.map_comp]
    rw [← tensorHom_comp_tensorHom_assoc, ← H.map_comp]
    have h := τ.naturality x y
    change (β_ K (x ⟶[Complex R] y)).hom ≫
      (F.map x y ⊗ₘ τ.app y) ≫ eComp (Complex R) _ _ _ =
      (τ.app x ⊗ₘ G.map x y) ≫ eComp (Complex R) _ _ _ at h
    simpa only [Category.assoc] using
      congrArg (fun f => f ≫ H.map (F.obj x) (G.obj y)) h

/-- 概要：全次数自然変換を dg 関手で前合成する。
方針：各成分を対象写像で引き戻し、braiding の自然性で Hom 写像と交換する。
規約：KST §3.1。使われ方：二重 opposite と局所評価の構造を保つ比較。 -/
def dgGradedWhiskerLeft (H : DGFunctor R C D) {F G : DGFunctor R D E}
    (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) F G) :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj K)
      (H.comp F) (H.comp G) where
  app x := τ.app (H.obj x)
  naturality x y := by
    change (β_ K (x ⟶[Complex R] y)).hom ≫
      ((H.map x y ≫ F.map (H.obj x) (H.obj y)) ⊗ₘ τ.app (H.obj y)) ≫
        eComp (Complex R) _ _ _ =
      (τ.app (H.obj x) ⊗ₘ (H.map x y ≫ G.map (H.obj x) (H.obj y))) ≫
        eComp (Complex R) _ _ _
    have h := congrArg (fun f => (𝟙 K ⊗ₘ H.map x y) ≫ f)
      (τ.naturality (H.obj x) (H.obj y))
    change (𝟙 K ⊗ₘ H.map x y) ≫ (β_ K _).hom ≫
        (F.map (H.obj x) (H.obj y) ⊗ₘ τ.app (H.obj y)) ≫ eComp (Complex R) _ _ _ =
      (𝟙 K ⊗ₘ H.map x y) ≫
        (τ.app (H.obj x) ⊗ₘ G.map (H.obj x) (H.obj y)) ≫ eComp (Complex R) _ _ _ at h
    rw [BraidedCategory.braiding_naturality_assoc] at h
    simpa only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id] using h

end SerrePositivity.KST.DerivedBlowup
