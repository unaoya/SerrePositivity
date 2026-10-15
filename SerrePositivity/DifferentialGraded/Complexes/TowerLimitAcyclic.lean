module
public import SerrePositivity.DifferentialGraded.Complexes.TowerPrimitives
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # 全射的acyclic複体の可算逆極限のacyclic性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A]

lemma complexLimitDegree_element_ext {J : Type*} [Category* J]
    {F : J ⥤ Complex A} {c : Cone F} (hc : IsLimit c) (q : ℤ)
    [PreservesLimit F (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q)]
    {z w : c.pt.X q} (h : ∀ j, (c.π.app j).f q z = (c.π.app j).f q w) : z = w := by
  have hm : moduleElementMap A _ z = moduleElementMap A _ w := by
    apply (isLimitOfPreserves (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q) hc).hom_ext
    intro j
    apply (moduleElementEquiv A _).injective
    change (c.π.app j).f q ((1 : A) • z) = (c.π.app j).f q ((1 : A) • w)
    simpa only [one_smul] using h j
  have he := congrArg (fun a => a (1 : A)) hm
  change (1 : A) • z = (1 : A) • w at he
  simpa only [one_smul] using he

lemma complexTowerLimit_acyclic (F : ℕᵒᵖ ⥤ Complex A) {c : Cone F} (hc : IsLimit c)
    (hF : ∀ n, (F.obj (op n)).Acyclic)
    (hr : ∀ (n : ℕ) (q : ℤ), Function.Surjective
      ((F.map (homOfLE (n.le_add_right 1)).op).f q)) : c.pt.Acyclic := by
  intro q
  apply (HomologicalComplex.exactAt_iff' (K := c.pt)
    (i := q - 1) (j := q) (k := q + 1) (by simp) (by simp)).2
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ z : c.pt.X q, c.pt.d q (q + 1) z = 0 →
    ∃ t : c.pt.X (q - 1), c.pt.d (q - 1) q t = z
  intro z hz
  have hcycles (n : ℕ) : (F.obj (op n)).d q (q + 1) ((c.π.app (op n)).f q z) = 0 := by
    have he := congrArg (fun a => a z) ((c.π.app (op n)).comm q (q + 1))
    change (F.obj (op n)).d q (q + 1) ((c.π.app (op n)).f q z) =
      (c.π.app (op n)).f (q + 1) (c.pt.d q (q + 1) z) at he
    exact he.trans (by rw [hz, map_zero])
  have hcompat (n : ℕ) :
      (F.map (homOfLE (n.le_add_right 1)).op).f q ((c.π.app (op (n + 1))).f q z) =
        (c.π.app (op n)).f q z := by
    exact congrArg (fun a => a.f q z) (c.w (homOfLE (n.le_add_right 1)).op)
  obtain ⟨t, hdt, htcompat⟩ := complexTower_compatible_primitives
    (fun n => F.obj (op n)) (fun n => F.map (homOfLE (n.le_add_right 1)).op)
    hF hr q (fun n => (c.π.app (op n)).f q z) hcycles hcompat
  let tc : Cone (F ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) (q - 1)) :=
    { pt := 𝟙_ (ModuleCat A)
      π := NatTrans.ofOpSequence (fun n => moduleElementMap A _ (t n)) (by
        intro n
        apply (moduleElementEquiv A _).injective
        change (1 : A) • t n =
          (F.map (homOfLE (n.le_add_right 1)).op).f (q - 1) ((1 : A) • t (n + 1))
        simpa only [one_smul] using (htcompat n).symm) }
  let hl := isLimitOfPreserves (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) (q - 1)) hc
  let b := hl.lift tc (1 : A)
  have hb (n : ℕ) : (c.π.app (op n)).f (q - 1) b = t n := by
    have he := congrArg (fun a => a (1 : A)) (hl.fac tc (op n))
    change (c.π.app (op n)).f (q - 1) b = (1 : A) • t n at he
    exact he.trans (one_smul A _)
  refine ⟨b, ?_⟩
  apply complexLimitDegree_element_ext A hc q
  intro n
  have he := congrArg (fun a => a b) ((c.π.app n).comm (q - 1) q)
  change (F.obj n).d (q - 1) q ((c.π.app n).f (q - 1) b) =
    (c.π.app n).f q (c.pt.d (q - 1) q b) at he
  exact he.symm.trans ((congrArg ((F.obj n).d (q - 1) q) (hb n.unop)).trans (hdt n.unop))

end SerrePositivity.DifferentialGraded
