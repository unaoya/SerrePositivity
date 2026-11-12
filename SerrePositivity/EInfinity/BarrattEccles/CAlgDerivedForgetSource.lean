module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantAlgebraRelativeInput
public import SerrePositivity.EInfinity.SimplicialLocalization.WeakNerveInverts
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource

/-!
# 元の E 代数忘却から既存 D(R) への実反転関手

概要：元の cofibrant 入力の全単体を同じ底の複体へ送り、既存 D(R) へ解像する。
方針：Hom の宇宙を変えず単体ごとに元の通常忘却を後合成する。
規約：元の対象と全射を保持し、元の擬同型辺を反転する。
使われ方：完成した CAlg_R の普遍性への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet SimplicialLocalization
open scoped Simplicial
variable (A : Type u) [CommRing A]

def cofibrantAlgebraForgetNerve :
    nerve (cofibrantAlgebraRelativeCategory A).category ⟶ nerve (Complex A) where
  app _ := ↾fun Γ => Γ ⋙ cofibrantAlgebraDKForget A
  naturality := by
    intro d e α
    apply ConcreteCategory.hom_ext
    intro Γ
    rfl

lemma cofibrantAlgebraForgetNerve_mk₁
    {X Y : (cofibrantAlgebraRelativeCategory A).category} (f : X ⟶ Y) :
    (cofibrantAlgebraForgetNerve A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ ((cofibrantAlgebraDKForget A).map f) := by
  refine ComposableArrows.ext₁ rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

def cofibrantAlgebraUnderlyingDerivedSource :
    nerve (cofibrantAlgebraRelativeCategory A).category ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A :=
  cofibrantAlgebraForgetNerve A ≫ ComplexLimits.complexOrdinaryDerivedSource A

lemma cofibrantAlgebraUnderlyingDerivedSource_map_weak
    {X Y : (cofibrantAlgebraRelativeCategory A).category} (f : X ⟶ Y)
    (hf : (cofibrantAlgebraRelativeCategory A).weakEquivalences f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      ((nerve.edgeMk f).map (cofibrantAlgebraUnderlyingDerivedSource A)).toTruncated := by
  have hq : QuasiIso ((cofibrantAlgebraDKForget A).map f) :=
    (cofibrantAlgebraDKForgetRelative A).map f hf
  have h := ComplexLimits.complexOrdinaryDerivedSource_map_weak A
    ((cofibrantAlgebraDKForget A).map f) hq
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := ((nerve.edgeMk
    ((cofibrantAlgebraDKForget A).map f)).map
      (ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated) ?_).mp h
  change (ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ ((cofibrantAlgebraDKForget A).map f)) =
    (ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
      ((cofibrantAlgebraForgetNerve A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f))
  rw [cofibrantAlgebraForgetNerve_mk₁]

lemma cofibrantAlgebraUnderlyingDerivedSource_inverts :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (cofibrantAlgebraUnderlyingDerivedSource A)
      (weakNerveEdges (cofibrantAlgebraRelativeCategory A)) :=
  weakNerveEdges_inverts_of_arrows (cofibrantAlgebraRelativeCategory A)
    (cofibrantAlgebraUnderlyingDerivedSource A)
    (fun f hf => cofibrantAlgebraUnderlyingDerivedSource_map_weak A f hf)

end SerrePositivity.EInfinity.BarrattEccles
