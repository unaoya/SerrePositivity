module
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：有限な形状 K に対する内部 Hom Fun(K,−) は通常の filtered 余極限を保つ。
方針：各次数で Hom(K × Δ[n],−) と同型にし、有限表示性を使う。
規約：本モジュールの余極限は単体集合圏の strict 図式の余極限。
使われ方：coherent な filtered 余極限との比較に用いる有限形状の連続性。

対応節は Kerodon 3.6（Tag 012Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.ComparisonWithTopologicalSpaces

/-- 概要：内部 Hom の各次数の単体は K × Δ[n] からの射と自然に全単射。
方針：標準単体の Yoneda 表示と内部 Hom 随伴を合成する。
規約：K の有限性はこの同型には不要。使われ方：次数ごとの保存性。 -/
def internalHomEvaluationIso (K : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    ihom K ⋙ (evaluation _ _).obj n ≅
      coyoneda.obj (Opposite.op (K ⊗ stdSimplex.obj n.unop)) :=
  NatIso.ofComponents (fun X ↦ Equiv.toIso
    (SSet.yonedaEquiv.symm.trans ((ihom.adjunction K).homEquiv _ _).symm)) (by
      intro X Y f
      apply ConcreteCategory.hom_ext
      intro x
      change uncurry (SSet.yonedaEquiv.symm (((ihom K).map f).app n x)) =
        uncurry (SSet.yonedaEquiv.symm x) ≫ f
      rw [← SSet.yonedaEquiv_symm_comp, uncurry_natural_right])

/-- 概要：有限形状からの内部 Hom は小さい filtered 余極限を保存する。
方針：有限な K × Δ[n] の有限表示性による保存を評価関手で束ねる。
規約：小圏の宇宙は単体集合の宇宙と同じ。使われ方：有限指数の連続性。 -/
@[kerodon 03X6]
instance finiteInternalHom_preservesFilteredColimits (K : SSet.{u}) [K.Finite] :
    PreservesFilteredColimitsOfSize.{u, u} (ihom K) where
  preserves_filtered_colimits J _ _ := by
    apply preservesColimitsOfShape_of_evaluation
    intro n
    have : PreservesColimitsOfShape J
        (coyoneda.obj (Opposite.op (K ⊗ stdSimplex.obj n.unop))) := inferInstance
    exact preservesColimitsOfShape_of_natIso (internalHomEvaluationIso K n).symm

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.ComparisonWithTopologicalSpaces
