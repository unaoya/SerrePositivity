module
public import SerrePositivity.DifferentialGraded.Category.Homotopy

/-! # dg 関手と H⁰ 上の関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- dg 関手は Mathlib の Ch(A) 豊穣関手をそのまま用いる。 -/
abbrev DGFunctor (D : Type v) (E : Type w) [DGCategory A D] [DGCategory A E] :=
  EnrichedFunctor (Complex A) D E

variable {A} {D : Type v} {E : Type w} {T : Type t}
  [DGCategory A D] [DGCategory A E] [DGCategory A T]
namespace DGFunctor

/-- dg 恒等関手。 -/
abbrev id (D : Type v) [DGCategory A D] : DGFunctor A D D :=
  EnrichedFunctor.id (Complex A) D

/-- dg 関手の合成。Hom の chain map は同じ順に合成する。 -/
abbrev comp (F : DGFunctor A D E) (G : DGFunctor A E T) : DGFunctor A D T :=
  EnrichedFunctor.comp (Complex A) F G

/-- Z⁰ への制限。 -/
abbrev onClosed (F : DGFunctor A D E) : ClosedCategory A D ⥤ ClosedCategory A E := F.forget

/-- dg 関手の Z⁰ への制限は加法的。 -/
instance onClosedAdditive (F : DGFunctor A D E) : F.onClosed.Additive where
  map_add := by
    intro x y f g
    change (ForgetEnrichment.homTo (Complex A) f + ForgetEnrichment.homTo (Complex A) g) ≫
      F.map (ForgetEnrichment.to (Complex A) x) (ForgetEnrichment.to (Complex A) y) =
      ForgetEnrichment.homTo (Complex A) f ≫
        F.map (ForgetEnrichment.to (Complex A) x) (ForgetEnrichment.to (Complex A) y) +
      ForgetEnrichment.homTo (Complex A) g ≫
        F.map (ForgetEnrichment.to (Complex A) x) (ForgetEnrichment.to (Complex A) y)
    apply Preadditive.add_comp

/-- dg 関手の Z⁰ への制限は A 線形。 -/
instance onClosedLinear (F : DGFunctor A D E) : F.onClosed.Linear A where
  map_smul := by
    intro x y f a
    change (a • ForgetEnrichment.homTo (Complex A) f) ≫
      F.map (ForgetEnrichment.to (Complex A) x) (ForgetEnrichment.to (Complex A) y) =
      a • (ForgetEnrichment.homTo (Complex A) f ≫
        F.map (ForgetEnrichment.to (Complex A) x) (ForgetEnrichment.to (Complex A) y))
    apply CategoryTheory.Linear.smul_comp

/-- dg 関手は境界関係を保存する。Hom chain map とホモトピーの後合成を用いる。 -/
lemma preserves_boundary (F : DGFunctor A D E) {x y : ClosedCategory A D}
    (f g : x ⟶ y) (h : boundaryRelation A D f g) :
    boundaryRelation A E (F.onClosed.map f) (F.onClosed.map g) :=
  ⟨h.some.compRight (F.map x y)⟩

/-- 境界商の普遍性による H⁰ 関手。 -/
def onHomotopy (F : DGFunctor A D E) : HomotopyCategory A D ⥤ HomotopyCategory A E :=
  CategoryTheory.Quotient.lift _ (F.onClosed ⋙ toHomotopy A E) (by
    intro x y f g h
    apply (toHomotopy_map_eq_iff A E _ _).2
    exact F.preserves_boundary f g h)

/-- 商への関手の四角形は可換。 -/
lemma onHomotopy_fac (F : DGFunctor A D E) :
    toHomotopy A D ⋙ F.onHomotopy = F.onClosed ⋙ toHomotopy A E :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- H⁰ 関手は加法的。 -/
instance onHomotopyAdditive (F : DGFunctor A D E) : F.onHomotopy.Additive := by
  have : (toHomotopy A D ⋙ F.onHomotopy).Additive := by
    rw [onHomotopy_fac]
    infer_instance
  exact CategoryTheory.Functor.additive_of_full_essSurj_comp (toHomotopy A D) F.onHomotopy

/-- H⁰ 関手は A 線形。 -/
instance onHomotopyLinear (F : DGFunctor A D E) : F.onHomotopy.Linear A := by
  have : (toHomotopy A D ⋙ F.onHomotopy).Linear A := by
    rw [onHomotopy_fac]
    infer_instance
  exact CategoryTheory.Functor.linear_of_full_essSurj_comp (toHomotopy A D) F.onHomotopy

/-- H⁰ 関手は恒等関手を保存する。 -/
lemma onHomotopy_id : (id (A := A) D).onHomotopy = 𝟭 (HomotopyCategory A D) := by
  apply Quotient.lift_unique'
  apply CategoryTheory.Functor.ext
  · intro x y f
    simp [onHomotopy, EnrichedFunctor.forget, EnrichedFunctor.id,
      CategoryTheory.Quotient.lift, CategoryTheory.Quotient.functor, id]
  · intro x
    rfl

/-- H⁰ 関手は合成を保存する。 -/
lemma onHomotopy_comp (F : DGFunctor A D E) (G : DGFunctor A E T) :
    (comp F G).onHomotopy = F.onHomotopy ⋙ G.onHomotopy := by
  apply Quotient.lift_unique'
  apply CategoryTheory.Functor.ext
  · intro x y f
    simp [onHomotopy, EnrichedFunctor.forget, EnrichedFunctor.comp,
      CategoryTheory.Quotient.lift, CategoryTheory.Quotient.functor, comp]
    rfl
  · intro x
    rfl
end DGFunctor
end SerrePositivity.DifferentialGraded
