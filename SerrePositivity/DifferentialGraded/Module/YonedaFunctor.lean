module
public import SerrePositivity.DifferentialGraded.Module.Yoneda
public import SerrePositivity.DifferentialGraded.Module.HomElementComposition
public import SerrePositivity.DifferentialGraded.Functor.Components

/-! # 全Hom endに値を持つdg Yoneda関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 代表対象のHomを代表加群間の全Hom endへ送る。 -/
def yonedaHom (x y : D) :
    (x ⟶[Complex A] y) ⟶ moduleHom A D (representable A x) (representable A y) :=
  (dgYonedaIso A x (representable A y)).inv

@[reassoc]
lemma yonedaHom_π (x y b : D) :
    yonedaHom A D x y ≫ moduleHomπ A D (representable A x) (representable A y) b =
      yonedaExtensionApp A x (representable A y) (𝟙 _) (op b) :=
  moduleHomEquiv_symm_π A D _ _ _ (yonedaExtension A x (representable A y) (𝟙 _)) b

lemma yonedaHom_element (x y b : D) {p r n : ℤ} (f : GradedHom A x y p)
    (h : GradedHom A b x r) (hn : r + p = n) :
    (((moduleHomπ A D (representable A x) (representable A y) b).f p
      ((yonedaHom A D x y).f p f)).v r n hn) h =
    (p * r).negOnePow • forward A h f hn := by
  have hp := congrArg (fun t => t.f p f) (yonedaHom_π A D x y b)
  change (moduleHomπ A D (representable A x) (representable A y) b).f p
    ((yonedaHom A D x y).f p f) = _ at hp
  rw [hp]
  have he := yonedaExtensionApp_apply A x (representable A y) (𝟙 _) (op b) p r n hn f h
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply] at he
  change (((yonedaExtensionApp A x (representable A y) (𝟙 _) (op b)).f p f).v r n hn) h =
    (p * r).negOnePow • forward A (D := D) (x := b) (y := x) (z := y) h f hn at he
  exact he

/-- 代表加群からのHomの斉次要素は単位元での評価で判定できる。 -/
lemma yoneda_element_ext (x : D) (M : RightModule A D) {q : ℤ}
    {t s : (moduleHom A D (representable A x) M).X q}
    (h : (((moduleHomπ A D (representable A x) M x).f q t).v 0 q (zero_add q))
        (unitElement A x).val =
      (((moduleHomπ A D (representable A x) M x).f q s).v 0 q (zero_add q))
        (unitElement A x).val) : t = s := by
  apply (ModuleCat.mono_iff_injective ((dgYonedaIso A x M).hom.f q)).mp inferInstance
  change (yonedaEvaluateFamily A x M
      (fun y => moduleHomπ A D (representable A x) M y.unop)).f q t =
    (yonedaEvaluateFamily A x M
      (fun y => moduleHomπ A D (representable A x) M y.unop)).f q s
  rw [yonedaEvaluateFamily_apply, yonedaEvaluateFamily_apply]
  exact h

lemma yoneda_moduleUnit_π (M : RightModule A D) (b : D) :
    (moduleHomπ A D M M b).f 0 (unitElement A M).val = Cochain.ofHom (𝟙 (M.obj (op b))) := by
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (moduleIdentity_π A D M b)
  rw [cycleFromUnit_postcomp, identity, cycleFromUnit_unitFromCycle] at h
  exact h

lemma yonedaHom_unit (x : D) :
    (yonedaHom A D x x).f 0 (unitElement A x).val = (unitElement A (representable A x)).val := by
  apply yoneda_element_ext A D x (representable A x)
  rw [yonedaHom_element, yoneda_moduleUnit_π, Cochain.ofHom_v]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, unit_forward,
    HomologicalComplex.id_f, ModuleCat.id_apply]

lemma yonedaHom_forward {x y z : D} {p q k : ℤ} (f : GradedHom A x y p)
    (g : GradedHom A y z q) (hk : p + q = k) :
    (yonedaHom A D x z).f k (forward A f g hk) =
      forward A (D := RightModule A D) (x := representable A x) (y := representable A y)
        (z := representable A z) ((yonedaHom A D x y).f p f) ((yonedaHom A D y z).f q g) hk := by
  apply yoneda_element_ext A D x (representable A z)
  rw [yonedaHom_element, moduleHomForward_π, Cochain.units_smul_v,
    Cochain.comp_v _ _ hk 0 p k (zero_add p) hk]
  change (k * 0).negOnePow • forward A (unitElement A x).val (forward A f g hk)
      (zero_add k) =
    (p * q).negOnePow •
      (((moduleHomπ A D (representable A y) (representable A z) x).f q
        ((yonedaHom A D y z).f q g)).v p k hk
          ((((moduleHomπ A D (representable A x) (representable A y) x).f p
            ((yonedaHom A D x y).f p f)).v 0 p (zero_add p)) (unitElement A x).val))
  rw [yonedaHom_element]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, forward_unit]
  rw [yonedaHom_element, mul_comm q p, smul_smul, Int.units_mul_self, one_smul]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, forward_unit]

/-- Mathlib豊穣関手としてのdg Yoneda。 -/
def dgYoneda : DGFunctor A D (RightModule A D) :=
  DGFunctor.ofHomMaps A (representable A) (yonedaHom A D)
    (yonedaHom_unit A D) (fun _ _ _ _ _ _ hk f g => yonedaHom_forward A D f g hk)

end SerrePositivity.DifferentialGraded
