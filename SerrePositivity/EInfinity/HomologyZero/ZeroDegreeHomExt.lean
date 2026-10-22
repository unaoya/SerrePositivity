module

public import SerrePositivity.EInfinity.HomologyZero.ZeroDegreeLinear
public import SerrePositivity.EInfinity.HomologyZero.PairingRepresentatives
public import SerrePositivity.DifferentialGraded.Complexes.Closed

/-!
# 零次集中源の単位元による射の判定

概要：零次集中源からの射と二入力射は、元の単位からの点で判定できる。
方針：全零次元を閉元として表し、二入力は curry と単位子の自然性に帰着する。
規約：標的には支持・平坦性の条件を課さない。
使われ方：標準 H⁰ 同型の積保存を元の代表射で証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.HomologyZero
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma zeroDegree_hom_ext (K : Complex A) [K.IsStrictlyLE 0] [K.IsStrictlyGE 0]
    {T : Complex A} (f g : K ⟶ T)
    (h : ∀ x : 𝟙_ (Complex A) ⟶ K, x ≫ f = x ≫ g) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · exact (K.isZero_of_isStrictlyGE 0 i hi).eq_of_src _ _
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun k => k.f 0 (1 : A))
      (h (unitFromCycle K ((componentCyclesLinearEquiv K) x)))
    simp only [HomologicalComplex.comp_f, unitFromCycle, mkHomFromSingle_f] at hx
    change f.f 0 ((1 : A) • x) = g.f 0 ((1 : A) • x) at hx
    simpa only [one_smul] using hx
  · exact (K.isZero_of_isStrictlyLE 0 i hi).eq_of_src _ _

lemma zeroDegree_pairing_ext (K L : Complex A)
    [K.IsStrictlyLE 0] [K.IsStrictlyGE 0] [L.IsStrictlyLE 0] [L.IsStrictlyGE 0]
    {T : Complex A} (f g : K ⊗ L ⟶ T)
    (h : ∀ (x : 𝟙_ (Complex A) ⟶ K) (y : 𝟙_ (Complex A) ⟶ L),
      unitPairing f x y = unitPairing g x y) : f = g := by
  apply (tensorRightHomEquiv L K T).injective
  apply zeroDegree_hom_ext K
  intro x
  have hx : (x ▷ L) ≫ f = (x ▷ L) ≫ g := by
    apply (cancel_epi (λ_ L).inv).mp
    apply zeroDegree_hom_ext L
    intro y
    have hy := h x y
    change (λ_ (𝟙_ (Complex A))).inv ≫ (x ⊗ₘ y) ≫ f =
      (λ_ (𝟙_ (Complex A))).inv ≫ (x ⊗ₘ y) ≫ g at hy
    simpa only [Category.assoc, leftUnitor_inv_naturality_assoc, tensorHom_def'] using hy
  change x ≫ curryRight f = x ≫ curryRight g
  have hc : curryRight ((x ⊗ₘ 𝟙 L) ≫ f) = curryRight ((x ⊗ₘ 𝟙 L) ≫ g) := by
    simpa only [tensorHom_id] using congrArg curryRight hx
  simpa only [curryRight_naturality_source] using hc

end SerrePositivity.EInfinity.HomologyZero
