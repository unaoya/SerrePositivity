module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomEnd

/-! # dg 関手 Hom end の全次数パラメータの普遍性
概要：Hom end への射と元の dg 関手間の GradedNatTrans を厳密に対応させる。
方針：等化子・全対象の積・chain curry の普遍性を使う。
規約：パラメータと全 Hom の自然性を保持する。使われ方：非離散 dg 関手 Hom の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E]
local instance : HasProductsOfShape D (ModuleCat.{u} A) := ModuleCat.hasLimitsOfShape
local instance : HasProductsOfShape (D × D) (ModuleCat.{u} A) := ModuleCat.hasLimitsOfShape

/-- Hom end に入るための条件は全次数の豊穣自然性と同値。 -/
lemma dgFunctorHomRelations_eq_iff (M N : DGFunctor A D E) {K : Complex A}
    (k : K ⟶ dgFunctorHomCandidates A D E M N) :
    k ≫ dgFunctorHomRelationsLeft A D E M N = k ≫ dgFunctorHomRelationsRight A D E M N ↔
      ∀ x y : D,
        (β_ K (x ⟶[Complex A] y)).hom ≫
          (M.map x y ⊗ₘ (k ≫ Pi.π (dgFunctorHomFamily A D E M N) y)) ≫
            eComp (Complex A) (M.obj x) (M.obj y) (N.obj y) =
        ((k ≫ Pi.π (dgFunctorHomFamily A D E M N) x) ⊗ₘ N.map x y) ≫
          eComp (Complex A) (M.obj x) (N.obj x) (N.obj y) := by
  constructor
  · intro h x y
    have hp := congrArg (fun f => f ≫ Pi.π (dgFunctorHomRelations A D E M N) (x, y)) h
    simp only [dgFunctorHomRelationsLeft, dgFunctorHomRelationsRight, Category.assoc,
      dgFunctorHomRelations, Pi.lift_comp_π] at hp
    have ht := congrArg uncurryRight hp
    rw [← curryRight_naturality_source, ← curryRight_naturality_source,
      uncurryRight_curryRight, uncurryRight_curryRight,
      dgFunctorHomNaturalityLeft_precomp, dgFunctorHomNaturalityRight_precomp] at ht
    exact ht
  · intro h
    apply Pi.hom_ext
    rintro ⟨x, y⟩
    simp only [dgFunctorHomRelationsLeft, dgFunctorHomRelationsRight, Category.assoc,
      dgFunctorHomRelations, Pi.lift_comp_π]
    rw [← curryRight_naturality_source, ← curryRight_naturality_source,
      dgFunctorHomNaturalityLeft_precomp, dgFunctorHomNaturalityRight_precomp, h x y]

/-- パラメータ K を持つ全次数の豊穣自然変換。Mathlib の GradedNatTrans を再利用する。 -/
abbrev DGFunctorParamTrans (K : Complex A) (M N : DGFunctor A D E) :=
  GradedNatTrans ((Center.ofBraided (Complex A)).obj K) M N

/-- Hom end の普遍性：射 K→Hom(M,N) は K パラメータ付き豊穣自然変換。 -/
def dgFunctorHomEquiv (K : Complex A) (M N : DGFunctor A D E) :
    (K ⟶ dgFunctorHom A D E M N) ≃ DGFunctorParamTrans A D E K M N where
  toFun f :=
    { app x := f ≫ dgFunctorHomπ A D E M N x
      naturality x y := by
        have hh := congrArg (fun l => f ≫ l) (equalizer.condition
          (dgFunctorHomRelationsLeft A D E M N) (dgFunctorHomRelationsRight A D E M N))
        rw [← Category.assoc, ← Category.assoc] at hh
        have hp := (dgFunctorHomRelations_eq_iff A D E M N _).1 hh x y
        exact hp }
  invFun τ := equalizer.lift (Pi.lift (fun x => τ.app x)) (by
    apply (dgFunctorHomRelations_eq_iff A D E M N _).2
    intro x y
    simp only [dgFunctorHomFamily, Pi.lift_comp_π]
    exact τ.naturality x y)
  left_inv f := by
    apply dgFunctorHom_ext
    intro x
    simp only [dgFunctorHomπ, equalizer.lift_ι_assoc, Pi.lift_comp_π]
  right_inv τ := by
    apply GradedNatTrans.ext
    funext x
    simp only [dgFunctorHomπ, equalizer.lift_ι_assoc, Pi.lift_comp_π]
/-- Hom end に持ち上げた自然変換の評価は元の成分。 -/
@[reassoc (attr := simp)]
lemma dgFunctorHomEquiv_symm_π (K : Complex A) (M N : DGFunctor A D E)
    (τ : DGFunctorParamTrans A D E K M N) (x : D) :
    (dgFunctorHomEquiv A D E K M N).symm τ ≫ dgFunctorHomπ A D E M N x = τ.app x := by
  simp only [dgFunctorHomEquiv, Equiv.coe_fn_symm_mk, dgFunctorHomπ,
    equalizer.lift_ι_assoc, Pi.lift_comp_π]
/-- Hom end の評価族は全豊穣 Hom に関して自然。 -/
lemma dgFunctorHomπ_naturality (M N : DGFunctor A D E) (x y : D) :
    (β_ (dgFunctorHom A D E M N) (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ dgFunctorHomπ A D E M N y) ≫ eComp (Complex A) _ _ _ =
    (dgFunctorHomπ A D E M N x ⊗ₘ N.map x y) ≫ eComp (Complex A) _ _ _ := by
  have h := (dgFunctorHomEquiv A D E (dgFunctorHom A D E M N) M N (𝟙 _)).naturality x y
  change (β_ (dgFunctorHom A D E M N) (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ (𝟙 _ ≫ dgFunctorHomπ A D E M N y)) ≫ eComp (Complex A) _ _ _ =
    ((𝟙 _ ≫ dgFunctorHomπ A D E M N x) ⊗ₘ N.map x y) ≫ eComp (Complex A) _ _ _ at h
  simpa only [Category.id_comp] using h
end SerrePositivity.KST.SConstruction
