module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientMonoidAction
public import SerrePositivity.EInfinity.BarrattEccles.CAlgDiscreteDerivedComparison
public import SerrePositivity.EInfinity.Interface.StrictInputs
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport
import all SerrePositivity.EInfinity.Interface.StrictInputs

/-!
# 厳密な可換 dg 代数の導来像

## 概要
HA §7.1.3 の厳密入力を Barratt–Eccles 代数の局所化に送る。

## 方針
augmentation に沿う制限を厳密代数の局所化源と合成する。

## 規約
次数零の入力と忘却後の複体には、界面で指定した関手を使う。

## 使われ方
BS 著者版 Theorem 6.2 の cdga 入力。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory DifferentialGraded SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 厳密な可換 dg 代数の Barratt–Eccles の局所化での像。 -/
def barrattEcclesOfCdga : nerve (CommMon (Complex A)) ⟶ CAlg_R A :=
  nerveMap (cdgaAlgebraFunctor A) ≫ algebraCAlgSource A

/-- 厳密な可換 dg 代数の底は元の複体の導来像。 -/
def barrattEcclesOfCdga_forget :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (barrattEcclesOfCdga A ≫ cAlgForgetDerived A)
      (nerveMap (CommMon.forget (Complex A)) ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) := by
  let F := cdgaAlgebraFunctor A
  let U := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)
  have h : nerveMap F ≫ nerveMap U = nerveMap (CommMon.forget (Complex A)) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro Γ
    change (Γ ⋙ F) ⋙ U = Γ ⋙ CommMon.forget (Complex A)
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro i j g
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((algebraCAlgSource_underlyingDerivedIso A).precomp (nerveMap F))
  · simp only [barrattEcclesOfCdga, Category.assoc, F]
  · rw [algebraUnderlyingDerivedSource, ← Category.assoc, h]

/-- The two strict nerves agree on degree-zero CDGA inputs. -/
theorem cdgaDiscreteNerve_eq :
    nerveMap (discreteCDGA A) ≫ nerveMap (cdgaAlgebraFunctor A) =
      nerveMap (commAlgCatEquivUnder (CommRingCat.of A)).inverse ≫
        nerveMap (discreteAlgebraFunctor A) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  change (Γ ⋙ discreteCDGA A) ⋙ cdgaAlgebraFunctor A =
    (Γ ⋙ (commAlgCatEquivUnder (CommRingCat.of A)).inverse) ⋙ discreteAlgebraFunctor A
  unfold discreteCDGA
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j g
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
  rfl

/-- 次数零の cdga の像は元の離散代数の埋め込みに一致する。 -/
def barrattEcclesOfCdga_discrete :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap (discreteCDGA A) ≫ barrattEcclesOfCdga A)
      (discreteCAlgUnderEmbedding A) := by
  have h : nerveMap (discreteCDGA A) ≫ barrattEcclesOfCdga A =
      discreteCAlgUnderEmbedding A := by
    simp only [barrattEcclesOfCdga, discreteCAlgUnderEmbedding, discreteCAlgEmbedding,
      ← Category.assoc, cdgaDiscreteNerve_eq]
  exact eqToIso (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) h)

end SerrePositivity.EInfinity.BarrattEccles
