module
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

public import SerrePositivity.KST.Spectra.StandardSimplexLatching
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.RelativeBoundaryTensor
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
概要：パラメーターを tensor した標準単体の境界表示。
方針：tensor の左随伴性による余極限保存を有限単体表示へ適用する。
規約：パラメーターは任意の単体集合で Kan 性は不要。
使われ方：Goerss–Jardine VII §4、HTT A.3.3。Tot の相対 latching 射と pushout-product の比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.KST.Spectra.SimplexTensorBoundary

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：標準単体と一定のパラメーターとの tensor 図式。
方針：右 tensor 関手を標準単体図式へ後合成する。
規約：次数 j で Δ[j] ⊗ A。
使われ方：Goerss–Jardine VII §4。Tot の単体の随伴表示。 -/
abbrev diagram (A : SSet.{u}) : CosimplicialObject SSet.{u} :=
  SSet.stdSimplex ⋙ tensorRight A

/-- 概要：パラメーターの射が誘導する余単体自然変換。
方針：標準単体の因子を恒等にして左 whisker する。
規約：各段の射は Δ[j] ◁ f。
使われ方：Goerss–Jardine VII §4。Tot の horn の境界の射。 -/
def map {A B : SSet.{u}} (f : A ⟶ B) : diagram A ⟶ diagram B where
  app j := SSet.stdSimplex.obj j ◁ f
  naturality _ _ g := by
    change (SSet.stdSimplex.map g ▷ A) ≫ (SSet.stdSimplex.obj _ ◁ f) =
      (SSet.stdSimplex.obj _ ◁ f) ≫ (SSet.stdSimplex.map g ▷ B)
    exact whisker_exchange (SSet.stdSimplex.map g) f

/-- 概要：tensor した標準単体の境界 tensor は境界とパラメーターとの直積。
方針：右 tensor 関手の余極限保存による標準の同型を使う。
規約：同型の向きは表示された余極限から実際の境界の tensor へ。
使われ方：Goerss–Jardine VII §4。相対 latching の押し出しの比較。 -/
abbrev iso (A : SSet.{u}) (n : ℕ) :
    SubcomplexTensor.obj (SSet.boundary.{u} n) (diagram A) ≅
      (SSet.boundary.{u} n).toSSet ⊗ A :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.tensorIso (tensorRight A) (SSet.boundary.{u} n).toSSet

/-- 概要：境界 tensor の比較は境界包含を tensor した射と可換。
方針：有限 tensor の包含についての標準公式を使う。
規約：モデル圏の cofibration 類は用いない。
使われ方：HTT A.3.3。pushout-product の押し出しの第二辺。 -/
lemma iso_inclusion (A : SSet.{u}) (n : ℕ) :
    (iso A n).hom ≫ ((SSet.boundary.{u} n).ι ▷ A) =
      SubcomplexTensor.inclusion (SSet.boundary.{u} n) (diagram A) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.tensorIso_inclusion (tensorRight A) (SSet.boundary.{u} n)

/-- 概要：境界 tensor の比較同型はパラメーターの射に自然。
方針：境界表示の各余極限射で tensor の交換則を使う。
規約：厳密な射の等式。
使われ方：Goerss–Jardine VII §4。pushout-product の押し出しの第一辺。 -/
lemma iso_natural {A B : SSet.{u}} (f : A ⟶ B) (n : ℕ) :
    HomPresentation.tensorSourceMap (SubcomplexTensor.diagram (SSet.boundary.{u} n))
        (map f) ≫ (iso B n).hom =
      (iso A n).hom ≫ ((SSet.boundary.{u} n).toSSet ◁ f) := by
  apply colimit.hom_ext
  intro x
  rw [← Category.assoc, HomPresentation.ι_tensorSourceMap, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.ι_tensorIso_hom, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.ι_tensorIso_hom]
  exact (whisker_exchange
    ((NonsingularPresentation.cocone (SSet.boundary.{u} n).toSSet).ι.app x) f).symm

end

end SerrePositivity.KST.Spectra.SimplexTensorBoundary
