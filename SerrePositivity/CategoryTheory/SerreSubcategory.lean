module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Serre 部分圏とそのアーベル商

Serre 条件から有限積への閉包性を補い、充満部分圏をアーベル圏にする。
商のアーベル性自体には Mathlib の `SerreClassLocalization.abelian` を使う。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C) [P.IsSerreClass]

/-- Serre 部分圏は二項積で閉じる。直和の分裂短完全列を使う。 -/
instance serre_closedUnderBinaryProducts : P.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    have h₁ := p.prop_diag_obj (.mk .left)
    have h₂ := p.prop_diag_obj (.mk .right)
    let Y := p.diag.obj (.mk .left)
    let Z := p.diag.obj (.mk .right)
    have hprod : P (Y ⨯ Z) := P.prop_of_iso (biprod.isoProd Y Z) (P.prop_biprod h₁ h₂)
    exact P.prop_of_iso
      (IsLimit.conePointUniqueUpToIso (prodIsProd Y Z)
        ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)) hprod

instance serre_closedUnderFiniteProducts : P.IsClosedUnderFiniteProducts := .mk'

/-- Serre 部分圏はアーベル圏である。 -/
noncomputable example : Abelian P.FullSubcategory := inferInstance

/-- Serre 部分圏の包含は有限極限を保つ。 -/
noncomputable instance serreInclusionPreservesFiniteLimits : PreservesFiniteLimits P.ι := by
  have := P.preservesKernels_ι
  exact Functor.preservesFiniteLimits_of_preservesKernels P.ι

/-- Serre 部分圏の包含は有限余極限を保つ。 -/
noncomputable instance serreInclusionPreservesFiniteColimits : PreservesFiniteColimits P.ι := by
  have := P.preservesCokernels_ι
  exact Functor.preservesFiniteColimits_of_preservesCokernels P.ι

/-- 標準的な Serre 商には既存の局所化の構成からアーベル圏構造が入る。 -/
noncomputable instance serreQuotientAbelian : Abelian P.isoModSerre.Localization :=
  ObjectProperty.SerreClassLocalization.abelian P.isoModSerre.Q P

end SerrePositivity
