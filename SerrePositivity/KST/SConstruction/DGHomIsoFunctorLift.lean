module
public import SerrePositivity.KST.SConstruction.DGClosedIsoConjugation

/-! # 全 Hom 鎖同型を持つ実 dg 関手に沿う関手の持ち上げ
概要：対象を指定し、元の閉零同型を保ったまま実 dg 関手の全 Hom 作用を持ち上げる。
方針：元の関手を対象別同型で共役し、全 Hom 鎖同型の逆を合成して単位・合成を反映する。
規約：H⁰ の充満忠実性だけで代用しない。使われ方：標準 dg 対角の gluing への構成。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
private lemma liftUnitThroughIso {K : Type*} [Category K]
    {U V X Y : K} (a : U ⟶ X) (h : X ⟶ Y) (e : V ≅ Y) (u : U ⟶ V)
    (hh : a ≫ h = u ≫ e.hom) : a ≫ (h ≫ e.inv) = u := by
  rw [← Category.assoc, hh, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma liftCompositionThroughIso {K : Type*} [Category K] [MonoidalCategory K]
    {P₁ P₂ P₃ C₁ C₂ C₃ E₁ E₂ E₃ : K}
    (a : P₁ ⟶ E₁) (b : P₂ ⟶ E₂) (c : P₃ ⟶ E₃)
    (p : P₁ ⊗ P₂ ⟶ P₃) (q : C₁ ⊗ C₂ ⟶ C₃) (r : E₁ ⊗ E₂ ⟶ E₃)
    (e₁ : C₁ ≅ E₁) (e₂ : C₂ ≅ E₂) (e₃ : C₃ ≅ E₃)
    (hp : p ≫ c = (a ⊗ₘ b) ≫ r) (hq : q ≫ e₃.hom = (e₁.hom ⊗ₘ e₂.hom) ≫ r) :
    p ≫ (c ≫ e₃.inv) = ((a ≫ e₁.inv) ⊗ₘ (b ≫ e₂.inv)) ≫ q := by
  apply (cancel_mono e₃.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hq, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact hp

variable (R : Type u) [CommRing R]
  {C : Type v} [DGCategory R C] {E : Type w} [DGCategory R E]
  (J : DGFunctor R C E)
  (e : ∀ x y, homObject R C x y ≅ homObject R E (J.obj x) (J.obj y))
  (he : ∀ x y, (e x y).hom = J.map x y)
  {P : Type t} [DGCategory R P] (F : DGFunctor R P E) (b : P → C)
  (v : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ≅
    ForgetEnrichment.of (Complex R) (J.obj (b x)))

/-- 指定した同じ対象像へ、元の関手を閉零同型で共役した実 dg 関手。 -/
def dgHomIsoLiftTarget : DGFunctor R P E :=
  dgFunctorClosedConjugate R F (fun x => J.obj (b x)) v

/-- 指定対象と元の閉零同型を持つ、実 dg 関手の全 Hom での持ち上げ。 -/
def dgHomIsoFunctorLift : DGFunctor R P C where
  obj := b
  map x y := (dgHomIsoLiftTarget R J F b v).map x y ≫ (e (b x) (b y)).inv
  map_id x := by
    have hj : eId (Complex R) (b x) ≫ (e (b x) (b x)).hom =
        eId (Complex R) (J.obj (b x)) :=
      (congrArg (fun k => eId (Complex R) (b x) ≫ k) (he (b x) (b x))).trans (J.map_id (b x))
    exact liftUnitThroughIso _ _ _ _
      (((dgHomIsoLiftTarget R J F b v).map_id x).trans hj.symm)
  map_comp x y z := by
    have hj : eComp (Complex R) (b x) (b y) (b z) ≫ (e (b x) (b z)).hom =
        ((e (b x) (b y)).hom ⊗ₘ (e (b y) (b z)).hom) ≫
          eComp (Complex R) (J.obj (b x)) (J.obj (b y)) (J.obj (b z)) :=
      (congrArg (fun k => eComp (Complex R) (b x) (b y) (b z) ≫ k)
        (he (b x) (b z))).trans ((J.map_comp (b x) (b y) (b z)).trans
          (congrArg (fun k => k ≫
            eComp (Complex R) (J.obj (b x)) (J.obj (b y)) (J.obj (b z)))
              (congrArg₂ (fun f g => f ⊗ₘ g) (he (b x) (b y)).symm (he (b y) (b z)).symm)))
    exact liftCompositionThroughIso _ _ _ _ _ _ _ _ _
      ((dgHomIsoLiftTarget R J F b v).map_comp x y z) hj

/-- 持ち上げた関手は、元の指定対象を厳密に回収する。 -/
lemma dgHomIsoFunctorLift_obj (x : P) : (dgHomIsoFunctorLift R J e he F b v).obj x = b x := rfl

/-- 同じ持ち上げの全 Hom 鎖写像は、元の共役作用と同じ鎖同型の逆との合成。 -/
lemma dgHomIsoFunctorLift_map (x y : P) :
    (dgHomIsoFunctorLift R J e he F b v).map x y =
      (dgHomIsoLiftTarget R J F b v).map x y ≫ (e (b x) (b y)).inv := rfl

/-- 同じ持ち上げを元の実関手で送ると、元の対象別同型による共役関手を厳密に回収する。 -/
lemma dgHomIsoFunctorLift_factor :
    (dgHomIsoFunctorLift R J e he F b v).comp J = dgHomIsoLiftTarget R J F b v := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgHomIsoFunctorLift R J e he F b v).comp J)
    (G := dgHomIsoLiftTarget R J F b v) (fun _ => rfl)
  intro x y
  change (((dgHomIsoLiftTarget R J F b v).map x y ≫ (e (b x) (b y)).inv) ≫
    J.map (b x) (b y)) ≫ eqToHom (by rfl) = _
  erw [← he, eqToHom_refl, Category.comp_id, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 元の全 Hom 作用を回収する鎖写像は、同じ持ち上げの作用に一意に一致する。 -/
lemma dgHomIsoFunctorLift_map_unique (x y : P)
    (k : homObject R P x y ⟶ homObject R C (b x) (b y))
    (hk : k ≫ J.map (b x) (b y) = (dgHomIsoLiftTarget R J F b v).map x y) :
    k = (dgHomIsoFunctorLift R J e he F b v).map x y := by
  apply (cancel_mono (e (b x) (b y)).hom).mp
  change k ≫ (e (b x) (b y)).hom =
    ((dgHomIsoLiftTarget R J F b v).map x y ≫ (e (b x) (b y)).inv) ≫ (e (b x) (b y)).hom
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, he]
  exact hk

end SerrePositivity.KST.SConstruction
