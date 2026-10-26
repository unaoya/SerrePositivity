module
public import SerrePositivity.KST.SConstruction.DGFunctorClosedComparison
public import SerrePositivity.KST.SConstruction.DGFunctorHomPostcomposition

/-!
概要：全 Hom 自然な閉射族を厳密 dg 関手で後合成しても同じ全自然性を保持する。
方針：元自然性の式を元 Hom 写像で後合成し、前後合成の可換式を使う。
規約：元閉射の順方向を保持。使われ方：LT の実 connecting 比較を逆 shift する。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] {C : Type v} [DGCategory R C]
  {D : Type w} [DGCategory R D] {E : Type z} [DGCategory R E]

/-- 概要：単位パラメータの全 dg 比較は、その同じ閉射族の全 Hom 自然性を与える。
方針：元比較の自然性の両辺に単位の unitor を適用する。
規約：元成分を保持。使われ方：既存の dg 後合成を閉射比較へ接続する。 -/
lemma dgUnitComparison_hom_naturality (F G : DGFunctor R C D)
    (τ : DGFunctorParamTrans R C D (𝟙_ (Complex R)) F G) (x y : C) :
    F.map x y ≫ eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (F.obj x)) (ForgetEnrichment.homOf (Complex R) (τ.app y)) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (ForgetEnrichment.homOf (Complex R) (τ.app x))
        (ForgetEnrichment.of (Complex R) (G.obj y)) := by
  let t (c : C) : 𝟙_ (Complex R) ⟶ (F.obj c ⟶[Complex R] G.obj c) := τ.app c
  have h0 : (β_ (𝟙_ (Complex R)) (x ⟶[Complex R] y)).hom ≫
      (F.map x y ⊗ₘ t y) ≫ eComp (Complex R) _ _ _ =
    (t x ⊗ₘ G.map x y) ≫ eComp (Complex R) _ _ _ := τ.naturality x y
  have ht := congrArg (fun k => (λ_ (x ⟶[Complex R] y)).inv ≫ k) h0
  rw [braiding_tensorUnit_left] at ht
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at ht
  rw [rightUnitor_inv_comp_tensorHom_assoc, leftUnitor_inv_comp_tensorHom_assoc] at ht
  dsimp only [eHomWhiskerLeft, eHomWhiskerRight, eHomEquiv,
    ForgetEnrichment.enrichedOrdinaryCategory]
  exact ht

/-- 概要：同じ閉射族の厳密 dg 後合成は元全 Hom 自然性を保つ。
方針：既存のパラメータ付き dg 後合成と単位比較の全 Hom 回収を使う。
規約：元の全関手・全閉射を保持。使われ方：逆 shift 後の実 dg 比較。 -/
lemma dgClosedComparison_postcomp_naturality
    (F G : DGFunctor R C D) (H : DGFunctor R D E)
    (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
      ForgetEnrichment.of (Complex R) (G.obj x))
    (h : ∀ x y, F.map x y ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y))) (x y : C) :
    (F.comp H).map x y ≫ eHomWhiskerLeft (Complex R)
        (H.onClosed.obj (F.obj x)) (H.onClosed.map (a y)) =
      (G.comp H).map x y ≫ eHomWhiskerRight (Complex R)
        (H.onClosed.map (a x)) (H.onClosed.obj (G.obj y)) :=
  dgUnitComparison_hom_naturality R (F.comp H) (G.comp H)
    (dgFunctorParamPost R C D E H (dgFunctorClosedComparison R F G a h)) x y
end SerrePositivity.KST.SConstruction
