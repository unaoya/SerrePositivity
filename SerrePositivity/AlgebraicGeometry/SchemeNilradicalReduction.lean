module

public import SerrePositivity.AlgebraicGeometry.ProperFlatteningNoetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
概要：既存の nilradical の閉部分スキームを、G3 の被約化として使う。
方針：標準アフィン被覆の根基イデアルによる商は被約で、台は基底全体。
規約：局所有限表示性だけに Noether 性を使う。
使われ方：G3 の帰納で被約基底上の平坦化を適用する準備。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

/-- nilradical の実際の閉部分スキームは被約。 -/
instance schemeNilradicalSubscheme_isReduced (Y : Scheme.{u}) :
    _root_.AlgebraicGeometry.IsReduced Y.nilradical.subscheme := by
  haveI (U : Y.affineOpens) :
      _root_.IsReduced (Γ(Y, U) ⧸ Y.nilradical.ideal U) := by
    apply (RingHom.ker_isRadical_iff_reduced_of_surjective
      (f := Ideal.Quotient.mk (Y.nilradical.ideal U)) Ideal.Quotient.mk_surjective).mp
    rw [Ideal.mk_ker]
    change (Ideal.radical (⊥ : Ideal Γ(Y, U))).IsRadical
    exact Ideal.radical_isRadical _
  letI : ∀ U : Y.nilradical.subschemeCover.openCover.I₀,
      _root_.AlgebraicGeometry.IsReduced (Y.nilradical.subschemeCover.openCover.X U) := fun U ↦ by
    let V : Y.affineOpens := U
    change _root_.AlgebraicGeometry.IsReduced
      (Spec (CommRingCat.of (Γ(Y, V) ⧸ Y.nilradical.ideal V)))
    infer_instance
  exact _root_.AlgebraicGeometry.IsReduced.of_openCover _ Y.nilradical.subschemeCover.openCover

/-- nilradical の閉包含は位相的に全射。 -/
instance schemeNilradicalSubscheme_surjective (Y : Scheme.{u}) :
    Surjective Y.nilradical.subschemeι := by
  refine ⟨Set.range_eq_univ.mp ?_⟩
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]
  rfl

/-- Noether 基底では nilradical の閉包含は局所有限表示。 -/
instance schemeNilradicalSubscheme_locallyOfFinitePresentation (Y : Scheme.{u})
    [_root_.AlgebraicGeometry.IsNoetherian Y] :
    LocallyOfFinitePresentation Y.nilradical.subschemeι := inferInstance

end SerrePositivity.AlgebraicGeometry
