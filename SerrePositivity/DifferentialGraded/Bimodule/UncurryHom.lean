module
public import SerrePositivity.DifferentialGraded.Bimodule.TensorFunctor

/-! # bimoduleからtensor積dg圏上のHom射を構成する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex HomologicalComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- tensor積のHomを、右作用、左作用の豊穣順合成へ送る。 -/
def uncurryHom (M : Bimodule A B C) (x y : DGTensorCategory A Bᵒᵖ C) :
    (x ⟶[Complex A] y) ⟶ homComplex A (M.value x.1.unop x.2) (M.value y.1.unop y.2) :=
  ((M.rightAt x.2).map x.1 y.1 ⊗ₘ (M.leftAt y.1.unop).map x.2 y.2) ≫
    enrichedComposition _ _ _

/-- 純粋Homでのuncurryingの成分式。豊穣順の符号を保持する。 -/
lemma uncurryHom_apply (M : Bimodule A B C) {x y : DGTensorCategory A Bᵒᵖ C} {p q n : ℤ}
    (f : GradedHom A x.1 y.1 p) (g : GradedHom A x.2 y.2 q) (hn : p + q = n) :
    (M.uncurryHom x y).f n (dgTensorElement A f g hn) =
      (p * q).negOnePow • (((M.rightAt x.2).map x.1 y.1).f p f).comp
        (M.leftCochain g y.1.unop) hn := by
  change (enrichedComposition _ _ _).f n
    ((((M.rightAt x.2).map x.1 y.1) ⊗ₘ ((M.leftAt y.1.unop).map x.2 y.2)).f n
      (ιTensorObj (x.1 ⟶[Complex A] y.1) (x.2 ⟶[Complex A] y.2) p q n hn (f ⊗ₜ[A] g))) = _
  rw [tensorMap_apply]
  exact enrichedComposition_apply _ _ _ p q n hn _ _

/-- 任意複体を対象と見た単位のcycleは通常恒等cochain。 -/
lemma complex_unitElement (P : Complex A) :
    (unitElement A P).val = Cochain.ofHom (𝟙 P) := by
  change (cycleFromUnit _ (identity P)).val = _
  rw [identity, cycleFromUnit_unitFromCycle]

lemma leftCochain_unit (M : Bimodule A B C) (b : B) (c : C) :
    M.leftCochain (unitElement A c).val b = Cochain.ofHom (𝟙 (M.value b c)) := by
  rw [leftCochain_eq]
  exact (DGFunctor.map_unitElement A (M.leftAt b) c).trans (complex_unitElement _)

/-- uncurryHomはtensor積の単位cycleを恒等cochainへ送る。 -/
lemma uncurryHom_unit (M : Bimodule A B C) (x : DGTensorCategory A Bᵒᵖ C) :
    (M.uncurryHom x x).f 0 (unitElement A x).val =
      Cochain.ofHom (𝟙 (M.value x.1.unop x.2)) := by
  rw [dgTensor_unitElement, uncurryHom_apply, leftCochain_unit]
  have h := DGFunctor.map_unitElement A (M.rightAt x.2).toFunctor x.1
  rw [complex_unitElement] at h
  have he := congrArg (fun f : Cochain (M.value x.1.unop x.2) (M.value x.1.unop x.2) 0 =>
    (0 * 0 : ℤ).negOnePow • f.comp (Cochain.ofHom (𝟙 (M.value x.1.unop x.2))) rfl) h
  exact he.trans (by simp)

/-- Hom射の単位cycle計算を、単位複体からの射の等式へ戻す。 -/
lemma uncurryHom_identity (M : Bimodule A B C) (x : DGTensorCategory A Bᵒᵖ C) :
    eId (Complex A) x ≫ M.uncurryHom x x = identity (M.value x.1.unop x.2) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (eId (Complex A) x ≫ M.uncurryHom x x)).val =
    (cycleFromUnit _ (identity (M.value x.1.unop x.2))).val
  rw [cycleFromUnit_postcomp, identity, cycleFromUnit_unitFromCycle]
  exact M.uncurryHom_unit x

end SerrePositivity.DifferentialGraded.Bimodule
