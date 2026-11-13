module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRepresentableDerivedZero
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientPretriangulated
public import SerrePositivity.DifferentialGraded.Verdier.Derived
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded DGQuotient
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

/-- tria の指定生成部分圏の retract 閉包に入る元の dg 対象。 -/
def dgThickClosureProperty (P : Set D) (x : D) : Prop :=
  (_root_.SerrePositivity.DifferentialGraded.triaImage R D P).retractClosure (_root_.SerrePositivity.DifferentialGraded.triaRepresentable R D x)

lemma dgThickClosureProperty_iff_perfect (P : Set D) (x : D) :
    dgThickClosureProperty R D P x ↔
      _root_.SerrePositivity.DifferentialGraded.modulePerfectOver R D P (_root_.SerrePositivity.DifferentialGraded.triaRepresentable R D x).obj :=
  _root_.SerrePositivity.DifferentialGraded.triaImage_retractClosure_iff_perfect R D P (_root_.SerrePositivity.DifferentialGraded.triaRepresentable R D x)

lemma dgThickClosureProperty_of_tria_retract (P : Set D) {x y : D}
    (r : Retract (_root_.SerrePositivity.DifferentialGraded.triaRepresentable R D x) (_root_.SerrePositivity.DifferentialGraded.triaRepresentable R D y))
    (hy : dgThickClosureProperty R D P y) : dgThickClosureProperty R D P x :=
  (_root_.SerrePositivity.DifferentialGraded.triaImage R D P).retractClosure.prop_of_retract r hy

lemma dgQuotient_vertex_isZero_iff_thick (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat R D P) (x : D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve R D P)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨x⟩ : QuotientObject D P)) ↔ dgThickClosureProperty R D P x := by
  let E := _root_.SerrePositivity.DifferentialGraded.DGQuotient.localQuotientTriaEquivalence R D P hP
  let Q := _root_.SerrePositivity.DifferentialGraded.triaQuotient R D P
  let X := _root_.SerrePositivity.DifferentialGraded.triaRepresentable R D x
  let Y := _root_.SerrePositivity.DifferentialGraded.triaRepresentable R (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) ⟨x⟩
  have hy : IsZero Y ↔ IsZero ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P)).obj
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.representable R (⟨x⟩ : _root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P)))) := by
    constructor
    · intro h
      exact (_root_.SerrePositivity.DifferentialGraded.triaInclusion R (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P)).map_isZero h
    · intro h
      exact IsZero.of_full_of_faithful_of_isZero (_root_.SerrePositivity.DifferentialGraded.triaInclusion R (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P)) Y h
  have hq : IsZero (Q.obj X) ↔ IsZero Y := by
    constructor
    · intro h
      exact (_root_.SerrePositivity.DifferentialGraded.DGQuotient.localQuotientTriaRepresentableIso R D P x).isZero_iff.mp
        (E.functor.map_isZero h)
    · intro h
      exact IsZero.of_full_of_faithful_of_isZero E.functor (Q.obj X)
        ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.localQuotientTriaRepresentableIso R D P x).isZero_iff.mpr h)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isZeroVertex_iff_representable_derived_isZero R
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) ⟨x⟩).trans (hy.symm.trans
      (hq.symm.trans (_root_.SerrePositivity.DifferentialGraded.verdierQuotient_isZero_iff_retractClosure (_root_.SerrePositivity.DifferentialGraded.triaImage R D P) X)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
