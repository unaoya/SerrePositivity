module

public import SerrePositivity.Asymptotic.SequenceComplex
public import SerrePositivity.HomologicalAlgebra.KProjectiveLift
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.StdBasis

/-!
# 列のホモトピー圏から導来圏の積への完全忠実性

共通有界な自由列の各段は K 射影的である。そのため各段で導来圏に移しても
射の集合は変わらない。鎖写像とホモトピーを段ごとに組み戻す結果と組み合わせ、
共通有界ホモトピー圏から加群の導来圏の積への完全忠実性を証明する。
これは有限 Postnikov 構成の接続に使うが、一様持ち上げ全体の存在はまだ主張しない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 共通有界な自由列の各段は K 射影的である。 -/
lemma evaluateComplex_isKProjective (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P) (n : ℕ) :
    ((evaluateComplex n).obj P).IsKProjective := by
  obtain ⟨a, b, h⟩ := evaluateComplex_uniform_bounds P hP
  have := (h n).2
  have (i : ℤ) : Projective (((evaluateComplex n).obj P).X i) :=
    ModuleCat.projective_of_free (Pi.basisFun R (Fin ((P.X i).rank n)))
  exact CochainComplex.isKProjective_of_projective _ b

variable [HasDerivedCategory (ModuleCat.{u} R)]

/-- 共通有界な自由列を、各段の導来圏の対象の列に移す関手。 -/
def pointwiseDerived : SequenceHomotopy R s ⥤ (ℕ → DerivedCategory (ModuleCat.{u} R)) where
  obj P n := DerivedCategory.Qh.obj (pointwiseHomotopy.obj P.obj n)
  map f n := DerivedCategory.Qh.map (pointwiseHomotopy.map f.hom n)
  map_id P := by funext n; simp
  map_comp f g := by funext n; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 導来圏の積への関手は忠実である。 -/
instance : (pointwiseDerived (R := R) (s := s)).Faithful where
  map_injective {P Q} f g h := by
    apply ObjectProperty.hom_ext
    apply pointwiseHomotopy.map_injective
    funext n
    have hb : strictlyBoundedComplex (FreeSequence R s) P.obj.as := by
      exact (boundedHomotopyProperty_quotient _ P.obj.as).1 P.property
    have := evaluateComplex_isKProjective P.obj.as hb n
    exact (CochainComplex.IsKProjective.Qh_map_bijective
      ((evaluateComplex n).obj P.obj.as) _).injective (congrFun h n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 導来圏の積への関手は充満である。 -/
instance : (pointwiseDerived (R := R) (s := s)).Full where
  map_surjective {P Q} f := by
    have hb : strictlyBoundedComplex (FreeSequence R s) P.obj.as := by
      exact (boundedHomotopyProperty_quotient _ P.obj.as).1 P.property
    have h (n : ℕ) : ∃ g : pointwiseHomotopy.obj P.obj n ⟶ pointwiseHomotopy.obj Q.obj n,
        DerivedCategory.Qh.map g = f n := by
      have := evaluateComplex_isKProjective P.obj.as hb n
      exact (CochainComplex.IsKProjective.Qh_map_bijective
        ((evaluateComplex n).obj P.obj.as) _).surjective (f n)
    choose g hg using h
    obtain ⟨k, hk⟩ := pointwiseHomotopy.map_surjective
      (show pointwiseHomotopy.obj P.obj ⟶ pointwiseHomotopy.obj Q.obj from g)
    refine ⟨ObjectProperty.homMk k, ?_⟩
    funext n
    change DerivedCategory.Qh.map (pointwiseHomotopy.map k n) = f n
    rw [hk]
    exact hg n

end SerrePositivity.Asymptotic
