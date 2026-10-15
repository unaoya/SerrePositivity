module
public import SerrePositivity.DifferentialGraded.Module.Left
public import SerrePositivity.DifferentialGraded.Module.Action

/-! # 左dg加群の全次数作用

共変豊穣関手のHom射を評価する。豊穣順合成と通常順合成のKoszul規約を保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 豊穣 Hom 射を評価する左加群の斉次作用。 -/
def leftAction (M : LeftModule A D) {x y : D} {p q n : ℤ}
    (f : GradedHom A x y p) (v : (M.obj x).X q) (hn : q + p = n) : (M.obj y).X n :=
  ((M.map x y).f p f).v q n hn v

/-- 左作用の単位則。 -/
lemma leftAction_unit (M : LeftModule A D) (x : D) (q : ℤ) (v : (M.obj x).X q) :
    leftAction A M (unitElement A x).val v (add_zero q) = v := by
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (M.map_id x)
  rw [cycleFromUnit_postcomp] at h
  change (M.map x x).f 0 (unitElement A x).val =
    (cycleFromUnit _ (identity (M.obj x))).val at h
  rw [identity, cycleFromUnit_unitFromCycle] at h
  unfold leftAction
  rw [h]
  rfl

/-- 作用は豊穣順の合成に対して Koszul 符号付きで結合する。 -/
lemma leftAction_forward (M : LeftModule A D) {x y z : D} {p q r m n s : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (v : (M.obj x).X r)
    (hm : p + q = m) (hs : r + p = s) (hn : r + m = n) :
    leftAction A M (forward A f g hm) v hn = (p * q).negOnePow •
      leftAction A M g (leftAction A M f v hs) (by omega) := by
  have h := M.map_comp x y z
  have hh := congrArg (fun l => l.f m
    (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q m hm (f ⊗ₜ[A] g))) h
  change (M.map x z).f m (forward A f g hm) = _ at hh
  change (M.map x z).f m (forward A f g hm) =
    (enrichedComposition _ _ _).f m
      (((M.map x y) ⊗ₘ (M.map y z)).f m
        (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q m hm (f ⊗ₜ[A] g))) at hh
  rw [tensorMap_apply] at hh
  change (M.map x z).f m (forward A f g hm) =
    (enrichedComposition _ _ _).f m
      (ιTensorObj (homComplex A (M.obj x) (M.obj y))
        (homComplex A (M.obj y) (M.obj z)) p q m hm
          (((M.map x y).f p f) ⊗ₜ[A] ((M.map y z).f q g))) at hh
  rw [enrichedComposition_apply] at hh
  unfold leftAction
  rw [hh, Cochain.units_smul_v, Cochain.comp_v _ _ hm r s n hs (by omega)]
  rfl

end SerrePositivity.DifferentialGraded
