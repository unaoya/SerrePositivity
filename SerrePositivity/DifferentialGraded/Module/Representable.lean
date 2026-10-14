module
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Complexes.Enrichment

/-! # 右代表 dg 加群

R_x(y)=Hom_D(y,x)。作用は豊穣合成の右tensor転置であり、全斉次射に作用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 代表右加群の Hom chain map。豊穣順の合成を右tensorで転置する。 -/
def representableMap (x : D) (y z : Dᵒᵖ) :
    (y ⟶[Complex A] z) ⟶ homComplex A (y.unop ⟶[Complex A] x) (z.unop ⟶[Complex A] x) :=
  curryRight (eComp (Complex A) z.unop y.unop x)

/-- 代表加群の作用の斉次公式。通常順では (-1)^(pk) が付く。 -/
lemma representableMap_apply (x : D) (y z : Dᵒᵖ) (p k n : ℤ) (hn : k + p = n)
    (f : GradedHom A y z p) (h : GradedHom A y.unop x k) :
    ((representableMap A x y z).f p f).v k n hn h =
      forward A (x := z.unop) (y := y.unop) (z := x) f h (by omega) := rfl

/-- 代表加群の閉単位の保存。 -/
lemma representableMap_id (x : D) (y : Dᵒᵖ) :
    eId (Complex A) y ≫ representableMap A x y y =
      identity (y.unop ⟶[Complex A] x) := by
  apply (unitCycleEquiv (homComplex A (y.unop ⟶[Complex A] x)
    (y.unop ⟶[Complex A] x))).injective
  apply Subtype.ext
  change (cycleFromUnit _ (eId (Complex A) y ≫ representableMap A x y y)).val =
    (cycleFromUnit _ (identity (y.unop ⟶[Complex A] x))).val
  rw [cycleFromUnit_postcomp, identity, cycleFromUnit_unitFromCycle]
  change (representableMap A x y y).f 0 (unitElement A y.unop).val =
    Cochain.ofHom (𝟙 (y.unop ⟶[Complex A] x))
  apply Cochain.ext₀
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  rw [representableMap_apply]
  change forward A (unitElement A y.unop).val h (zero_add k) = h
  exact forward_unit A h

/-- 代表加群の合成の保存。opposite の符号と Ch(A) の豊穣符号が一致する。 -/
lemma representableMap_comp (x : D) (y z w : Dᵒᵖ) :
    eComp (Complex A) y z w ≫ representableMap A x y w =
      (representableMap A x y z ⊗ₘ representableMap A x z w) ≫
        enrichedComposition (y.unop ⟶[Complex A] x) (z.unop ⟶[Complex A] x)
          (w.unop ⟶[Complex A] x) := by
  apply tensorHom_ext
  intro p q m hm
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change (representableMap A x y w).f m (forward A f g hm) = _
  rw [opposite_forward A D y z w p q m hm f g]
  simp only [Units.smul_def, map_zsmul]
  -- Evaluate the right-hand tensor map before comparing cochains.
  change (p * q).negOnePow •
    (representableMap A x y w).f m (forward A (x := w.unop) (y := z.unop) (z := y.unop)
      g f (by omega)) =
    (enrichedComposition _ _ _).f m
      (((representableMap A x y z) ⊗ₘ (representableMap A x z w)).f m
        (ιTensorObj (y ⟶[Complex A] z) (z ⟶[Complex A] w) p q m hm (f ⊗ₜ[A] g)))
  rw [tensorMap_apply, enrichedComposition_apply]
  apply Cochain.ext
  intro k n hkn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change ((p * q).negOnePow •
    ((representableMap A x y w).f m (forward A (x := w.unop) (y := z.unop) (z := y.unop)
      g f (by omega)))).v k n hkn h = _
  rw [Cochain.units_smul_v, Cochain.units_smul_v,
    Cochain.comp_v _ _ hm k (k + p) n rfl (by omega)]
  change (p * q).negOnePow • forward A (x := w.unop) (y := y.unop) (z := x)
      (forward A (x := w.unop) (y := z.unop) (z := y.unop) g f (by omega)) h (by omega) =
    (p * q).negOnePow • forward A (x := w.unop) (y := z.unop) (z := x) g
      (forward A (x := z.unop) (y := y.unop) (z := x) f h (by omega)) (by omega)
  exact congrArg (fun z => (p * q).negOnePow • z)
    (forward_assoc_of_sum A (w := w.unop) (x := z.unop) (y := y.unop) (z := x)
      g f h (a := m) (b := k + p) (by omega) (by omega) (by omega))

/-- 右代表 dg 加群。豊穣関手の単位・合成法則を上で証明する。 -/
abbrev representable (x : D) : RightModule A D where
  obj y := y.unop ⟶[Complex A] x
  map := representableMap A x
  map_id := representableMap_id A x
  map_comp := representableMap_comp A x
end SerrePositivity.DifferentialGraded
