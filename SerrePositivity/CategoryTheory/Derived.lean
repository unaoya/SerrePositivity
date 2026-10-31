module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import SerrePositivity.CategoryTheory.ExactDerivedTStructure
public import SerrePositivity.CategoryTheory.TStructure.Localization
public import SerrePositivity.CategoryTheory.Abelian.SerreLength

/-! # 導来圏の純な対象と Serre 商の導来圏

## 概要

単一次数にホモロジーをもつ導来対象をそのホモロジーで表示すること、Serre 部分圏にホモロジーをもつ対象による有界導来圏の商を与える。

## 方針

純な対象の表示は Mathlib の `exists_iso_singleFunctor_obj_of_isGE_of_isLE` による。商は `TStructure/Localization` の核による商の特殊化。

## 規約

純な対象の同型は今 `Classical.choice` で作っている。HomologicalAlgebra の `normalizedPureHomologyIso` と一本化して明示的な構成にする予定（計画 D の 3、区切り 1-3）。

## 使われ方

Asymptotic の長さの導来商。
-/

@[expose] public noncomputable section

universe w w₁ w₂

section DerivedPurePart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]

/-- 単一次数の導来対象は、その次数のホモロジーを置いた対象に同型。 -/
noncomputable def derivedPureHomologyIso (X : DerivedCategory A) (q : ℤ)
    [X.IsGE q] [X.IsLE q] :
    X ≅ (DerivedCategory.singleFunctor A q).obj
      ((DerivedCategory.homologyFunctor A q).obj X) := Classical.choice (by
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X q
  let h : (DerivedCategory.homologyFunctor A q).obj X ≅ M :=
    (DerivedCategory.homologyFunctor A q).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A q).app M
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor A q).mapIso h.symm⟩)

end SerrePositivity

end DerivedPurePart

section SerreDerivedQuotientPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Idempotents

variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [Category* B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- 完全関手の導来関手を有界導来圏に制限したもの。 -/
noncomputable abbrev boundedExactDerived : DerivedCategory.Bounded A ⥤ DerivedCategory B :=
  DerivedCategory.Bounded.ι ⋙ F.mapDerivedCategory

instance boundedExactDerived_tExact : (boundedExactDerived F).TExact
    DerivedCategory.TStructure.t.onBounded DerivedCategory.TStructure.t where
  rightTExact := Functor.RightTExact.mk _ _ _ (by
    intro X hX
    have := (DerivedCategory.TStructure.t.bounded.tStructure_isLE_iff _ X 0).1 hX
    exact Functor.isLE_obj F.mapDerivedCategory
      DerivedCategory.TStructure.t DerivedCategory.TStructure.t X.obj 0)
  leftTExact := Functor.LeftTExact.mk _ _ _ (by
    intro X hX
    have := (DerivedCategory.TStructure.t.bounded.tStructure_isGE_iff _ X 0).1 hX
    exact Functor.isGE_obj F.mapDerivedCategory
      DerivedCategory.TStructure.t DerivedCategory.TStructure.t X.obj 0)

/-- 有界導来圏上の核は、全ホモロジーが完全関手で零になる条件。 -/
lemma boundedExactDerived_kernel_iff (X : DerivedCategory.Bounded A) :
    triangulatedKernel (boundedExactDerived F) X ↔
      ∀ n : ℤ, IsZero (F.obj ((DerivedCategory.homologyFunctor A n).obj X.obj)) :=
  exactDerived_isZero_iff F X.obj

variable (P : ObjectProperty A) [P.IsSerreClass] [F.IsLocalization P.isoModSerre]

/-- Serre 商関手の導来関手の核は、全ホモロジーが Serre 部分圏に属する条件。 -/
lemma serreDerived_kernel_iff (X : DerivedCategory.Bounded A) :
    triangulatedKernel (boundedExactDerived F) X ↔
      ∀ n : ℤ, P ((DerivedCategory.homologyFunctor A n).obj X.obj) := by
  rw [boundedExactDerived_kernel_iff]
  exact forall_congr' (fun n ↦ ObjectProperty.SerreClassLocalization.isZero_obj_iff F P _)

/-- Serre 部分圏にホモロジーをもつ対象による有界導来圏の商。 -/
abbrev SerreDerivedQuotient := (triangulatedKernel (boundedExactDerived F)).trW.Localization

/-- Serre 導来商の t 構造。分母の切り詰め条件は証明済みの結果から供給する。 -/
noncomputable def serreDerivedQuotientTStructure : TStructure (SerreDerivedQuotient F) :=
  kernelQuotientTStructure (boundedExactDerived F)
    DerivedCategory.TStructure.t.onBounded DerivedCategory.TStructure.t

/-- 構成した Serre 導来商の t 構造は有界。 -/
lemma serreDerivedQuotient_bounded (X : SerreDerivedQuotient F) :
    (serreDerivedQuotientTStructure F).bounded X :=
  kernelQuotientTStructure_bounded _ _ _ (onBounded_bounded _) X

/-- Serre 導来商は冪等完備。 -/
lemma serreDerivedQuotient_isIdempotentComplete : IsIdempotentComplete (SerreDerivedQuotient F) :=
  kernelQuotient_isIdempotentComplete _ _ DerivedCategory.TStructure.t (onBounded_bounded _)

/-- Serre 導来商の形式的直和因子は、有界導来圏の実際の対象で代表できる。 -/
lemma serreDerivedQuotientKaroubi_has_representative (Y : Karoubi (SerreDerivedQuotient F)) :
    ∃ X : DerivedCategory.Bounded A,
      Nonempty ((toKaroubi _).obj
        ((triangulatedKernel (boundedExactDerived F)).trW.Q.obj X) ≅ Y) :=
  kernelQuotientKaroubi_has_representative _ _ DerivedCategory.TStructure.t
    (onBounded_bounded _) Y

/-- 代表対象には、実際に両側有界な複体を選べる。 -/
lemma serreDerivedQuotientKaroubi_has_bounded_complex (Y : Karoubi (SerreDerivedQuotient F)) :
    ∃ (X : DerivedCategory.Bounded A) (K : CochainComplex A ℤ) (a b : ℤ),
      K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧ Nonempty (X.obj ≅ DerivedCategory.Q.obj K) ∧
      Nonempty ((toKaroubi _).obj
        ((triangulatedKernel (boundedExactDerived F)).trW.Q.obj X) ≅ Y) := by
  obtain ⟨X, hX⟩ := serreDerivedQuotientKaroubi_has_representative F Y
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := X.property
  obtain ⟨K, hKa, hKb, e⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE X.obj a b
  exact ⟨X, K, a, b, hKa, hKb, e, hX⟩

end SerrePositivity

end SerreDerivedQuotientPart
