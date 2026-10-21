module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedCompositionKFlat
public import SerrePositivity.InfinityCategories.Derived.DGKernelGraphComparison
/-!
概要：graph による入力模型変更と、元の一般 kernel の実導来作用を比較する。
方針：graph の表現可能な列の相対 K-flat 性と、実導来合成の全関手比較を使う。
規約：元の kernel と dg 圏に平坦性を追加しない。
使われ方：cell 増大に沿う一般 kernel の入力模型移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C D E : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  [DGCategory R E] [Small.{u} E]
omit [Small.{u} C] in
/-- dg 関手の graph の各列は表現可能なので、右相対 K-flat。 -/
lemma dgFunctorGraph_rightRelativeKFlat (F : DGFunctor R C D) :
    Bimodule.rightRelativeKFlat R D C (functorGraph R C D F) := by
  intro c
  exact representable_relativeKFlat R D (F.obj c)
/-- graph による入力変更と元の kernel の合成は、同じ通常合成 kernel の実作用と全関手同型。 -/
def dgKernelDerivedInfinity_sourceGraphIso (F : DGFunctor R C D) (P : Bimodule R E D) :
    FunctorIso (dgModuleExtensionInfinity R C D F ≫ dgKernelDerivedInfinity R D E P)
      (dgKernelDerivedInfinity R C E
        (BimoduleTensor.compose R E D C P (functorGraph R C D F))) :=
  FunctorIso.postcomp (dgKernelDerivedInfinity_graphIso R C D F).symm
    (dgKernelDerivedInfinity R D E P) ≪≫
    dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R C D E (functorGraph R C D F) P
      (dgFunctorGraph_rightRelativeKFlat R C D F)
end SerrePositivity.InfinityCategories
