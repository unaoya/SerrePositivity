module
public import SerrePositivity.InfinityCategories.Derived.DGRepresentableDerivedZero
public import SerrePositivity.InfinityCategories.Derived.DGQuotientPretriangulated
public import SerrePositivity.DifferentialGraded.Verdier.NullObjects
/-!
概要：実 dg 商の零頂点を、代表対象の三角生成部分圏の retract 閉包で検出する。
方針：商の tria 比較と代表加群の零性を通じ、既存 Verdier 商の核判定を適用する。
規約：既存の安定閉包・指定零化集合・Verdier 辺は変更しない。
使われ方：D-16 の新しい thick 核包含の対象条件と実零対象の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGQuotient DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- tria の指定生成部分圏の retract 閉包に入る元の dg 対象。 -/
def dgThickClosureProperty (P : Set D) (x : D) : Prop :=
  (triaImage R D P).retractClosure (triaRepresentable R D x)

lemma dgThickClosureProperty_iff_perfect (P : Set D) (x : D) :
    dgThickClosureProperty R D P x ↔
      modulePerfectOver R D P (triaRepresentable R D x).obj :=
  triaImage_retractClosure_iff_perfect R D P (triaRepresentable R D x)

lemma dgThickClosureProperty_of_tria_retract (P : Set D) {x y : D}
    (r : Retract (triaRepresentable R D x) (triaRepresentable R D y))
    (hy : dgThickClosureProperty R D P y) : dgThickClosureProperty R D P x :=
  (triaImage R D P).retractClosure.prop_of_retract r hy

lemma dgQuotient_vertex_isZero_iff_thick (P : Set D) (hP : localKFlat R D P) (x : D) :
    IsZeroVertex (X := dgQuotientNerve R D P)
      (Simplex.vertex (⟨x⟩ : QuotientObject D P)) ↔ dgThickClosureProperty R D P x := by
  let E := localQuotientTriaEquivalence R D P hP
  let Q := triaQuotient R D P
  let X := triaRepresentable R D x
  let Y := triaRepresentable R (QuotientObject D P) ⟨x⟩
  have hy : IsZero Y ↔ IsZero ((moduleToDerived R (QuotientObject D P)).obj
      (ForgetEnrichment.of (Complex R) (representable R (⟨x⟩ : QuotientObject D P)))) := by
    constructor
    · intro h
      exact (triaInclusion R (QuotientObject D P)).map_isZero h
    · intro h
      exact IsZero.of_full_of_faithful_of_isZero (triaInclusion R (QuotientObject D P)) Y h
  have hq : IsZero (Q.obj X) ↔ IsZero Y := by
    constructor
    · intro h
      exact (localQuotientTriaRepresentableIso R D P x).isZero_iff.mp
        (E.functor.map_isZero h)
    · intro h
      exact IsZero.of_full_of_faithful_of_isZero E.functor (Q.obj X)
        ((localQuotientTriaRepresentableIso R D P x).isZero_iff.mpr h)
  exact (dgNerve_isZeroVertex_iff_representable_derived_isZero R
    (QuotientObject D P) ⟨x⟩).trans (hy.symm.trans
      (hq.symm.trans (verdierQuotient_isZero_iff_retractClosure (triaImage R D P) X)))

end SerrePositivity.InfinityCategories
