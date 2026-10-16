module
public import SerrePositivity.DifferentialGraded.Category.Comparison
public import SerrePositivity.DifferentialGraded.Complexes.Zero
public import Mathlib.Algebra.Homology.HomotopyCategory

/-! # 主dg複体圏のH⁰と既存の複体ホモトピー圏の線形同値

既存complex_boundary_iffで境界関係を照合し、Mathlibのホモトピー商を比較先として使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 閉零複体から通常複体への既存比較はA線形である。 -/
instance closedToComplexLinear : (closedToComplex A).Linear A where
  map_smul f a := by
    apply Cochain.ofHom_injective
    rw [Cochain.ofHom_smul]
    simp only [closedToComplex, complexClosedHomEquiv_cochain]
    rfl

/-- 主dg複体圏のH⁰から、既存の非有界複体ホモトピー圏への比較。 -/
def complexHomotopyComparison : HomotopyCategory A (Complex A) ⥤
    _root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ) :=
  CategoryTheory.Quotient.lift _
    (closedToComplex A ⋙ _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ))
    (by
      intro X Y f g h
      have hh := (complex_boundary_iff A X Y f g).mp h
      exact _root_.HomotopyCategory.eq_of_homotopy _ _ hh.some)

/-- 比較と商関手の四角形は、元の閉零比較と既存の商関手の合成に一致する。 -/
lemma complexHomotopyComparison_fac :
    toHomotopy A (Complex A) ⋙ complexHomotopyComparison A =
      closedToComplex A ⋙ _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ) :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- 主dg複体のH⁰比較は充満。既存の商射と閉零比較の充満性を使う。 -/
instance complexHomotopyComparisonFull : (complexHomotopyComparison A).Full where
  map_surjective {X Y} f := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨g, rfl⟩ := (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map_surjective f
    obtain ⟨h, rfl⟩ := (closedToComplex A).map_surjective g
    exact ⟨(toHomotopy A (Complex A)).map h, rfl⟩

/-- H⁰比較は忠実。既存の商での等式からchain homotopyを取り、主境界関係へ戻す。 -/
instance complexHomotopyComparisonFaithful : (complexHomotopyComparison A).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨f, rfl⟩ := (toHomotopy A (Complex A)).map_surjective f
    obtain ⟨g, rfl⟩ := (toHomotopy A (Complex A)).map_surjective g
    have hh := _root_.HomotopyCategory.homotopyOfEq
      ((closedToComplex A).map f) ((closedToComplex A).map g) h
    exact (toHomotopy_map_eq_iff A (Complex A) f g).mpr
      ((complex_boundary_iff A _ _ f g).mpr ⟨hh⟩)

/-- 対象は実際の複体のままなので、H⁰比較は本質的全射である。 -/
instance complexHomotopyComparisonEssSurj : (complexHomotopyComparison A).EssSurj where
  mem_essImage X :=
    ⟨(toHomotopy A (Complex A)).obj (ForgetEnrichment.of (Complex A) X.as), ⟨Iso.refl _⟩⟩

/-- 主dg複体のH⁰と既存の複体ホモトピー圏の比較は同値である。 -/
instance complexHomotopyComparisonIsEquivalence : (complexHomotopyComparison A).IsEquivalence where

/-- 任意可換環上の非有界複体についてのH⁰同値。 -/
def complexHomotopyEquivalence : HomotopyCategory A (Complex A) ≌
    _root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ) :=
  (complexHomotopyComparison A).asEquivalence

/-- H⁰比較の加法性は、商の充満・本質的全射性から降下する。 -/
instance complexHomotopyComparisonAdditive : (complexHomotopyComparison A).Additive := by
  have : (toHomotopy A (Complex A) ⋙ complexHomotopyComparison A).Additive := by
    rw [complexHomotopyComparison_fac]
    infer_instance
  exact Functor.additive_of_full_essSurj_comp (toHomotopy A (Complex A)) _

/-- H⁰比較は主Hom由来のスカラー作用を既存のホモトピー商のスカラー作用へ運ぶ。 -/
instance complexHomotopyComparisonLinear : (complexHomotopyComparison A).Linear A := by
  have : (toHomotopy A (Complex A) ⋙ complexHomotopyComparison A).Linear A := by
    rw [complexHomotopyComparison_fac]
    infer_instance
  exact Functor.linear_of_full_essSurj_comp (toHomotopy A (Complex A)) _

/-- 選択した同値の順関手はA線形であり、逆関手の線形性も同値の一般APIから得られる。 -/
instance complexHomotopyEquivalenceFunctorLinear :
    (complexHomotopyEquivalence A).functor.Linear A :=
  complexHomotopyComparisonLinear A

/-- 選択した同値の順関手は加法的であり、逆関手の加法性も継承される。 -/
instance complexHomotopyEquivalenceFunctorAdditive :
    (complexHomotopyEquivalence A).functor.Additive :=
  complexHomotopyComparisonAdditive A

end SerrePositivity.DifferentialGraded
