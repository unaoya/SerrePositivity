module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
概要：有限個の射と等式を、同じ有限段へ降ろす。
方針：局所有限表示の射の既存の因子化と有限型の射の一致判定を有限 cone にそろえる。
規約：元の極限射影と基底上の可換式を結論に保つ。
使われ方：G2 の gluing datum と細分の有限個の射・等式。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v
variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  {ι : Type v} [Finite ι] {S : Scheme.{u}}
  (D : ι → J ⥤ Scheme.{u}) (t : ∀ a, D a ⟶ (Functor.const J).obj S)
  (X : ι → Scheme.{u}) (f : ∀ a, X a ⟶ S)
  (c : ∀ a, Cone (D a)) (hc : ∀ a, IsLimit (c a))
  [∀ a, LocallyOfFinitePresentation (f a)]
  [∀ a {i j} (g : i ⟶ j), IsAffineHom ((D a).map g)]
  [∀ a i, CompactSpace ((D a).obj i)] [∀ a i, QuasiSeparatedSpace ((D a).obj i)]

include hc

/-- 有限個の基底上の射を、一つの共通する段へ実際の合成式を保って降ろす。 -/
theorem exists_finite_stage_maps_of_isLimit
    (a : ∀ b, (c b).pt ⟶ X b)
    (ha : ∀ b, (c b).π ≫ t b = (Functor.const J).map (a b ≫ f b)) :
    ∃ (j : J) (g : ∀ b, (D b).obj j ⟶ X b),
      ∀ b, (c b).π.app j ≫ g b = a b ∧ g b ≫ f b = (t b).app j := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose i g hg hgf using fun b ↦
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (D b) (t b) (f b) (c b) (hc b) (a b) (ha b)
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let q (b : ι) : j ⟶ i b := (hj (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩)).some
  refine ⟨j, fun b ↦ (D b).map (q b) ≫ g b, ?_⟩
  intro b
  constructor
  · rw [← Category.assoc, (c b).w, hg]
  · rw [Category.assoc, hgf]
    have hn := (t b).naturality (q b)
    change (D b).map (q b) ≫ (t b).app (i b) = (t b).app j ≫ 𝟙 S at hn
    exact hn.trans (Category.comp_id _)

/-- 有限個の射の等式が極限で成立すれば、一つの共通する後の段で全て成立する。 -/
theorem exists_finite_stage_equalities_of_isLimit {i : J}
    (a b : ∀ s, (D s).obj i ⟶ X s)
    (ha : ∀ s, (t s).app i = a s ≫ f s) (hb : ∀ s, (t s).app i = b s ≫ f s)
    (hab : ∀ s, (c s).π.app i ≫ a s = (c s).π.app i ≫ b s) :
    ∃ (j : J) (q : j ⟶ i), ∀ s, (D s).map q ≫ a s = (D s).map q ≫ b s := by
  choose j q hq using fun s ↦
    Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (D s) (t s) (f s) (c s) (hc s) (a s) (b s) (ha s) (hb s) (hab s)
  obtain ⟨k, g, r, hr⟩ := IsCofiltered.wideCospan q
  refine ⟨k, g, ?_⟩
  intro s
  have h := congrArg (fun z ↦ (D s).map (r s) ≫ z) (hq s)
  simpa only [← Category.assoc, ← Functor.map_comp, hr] using h

end SerrePositivity.AlgebraicGeometry
