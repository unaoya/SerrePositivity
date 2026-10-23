module

public import SerrePositivity.InfinityCategories.F2.Ind.SectionProductScaffoldValue
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorInitialEvaluation
public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldFirstVertex

/-!
概要：元の単体の初頂点での同じ切断評価は、全境界を持ち上げる。
方針：標準単体の同じ初頂点包含の left anodyne 性を既存の相対評価定理へ渡す。
規約：底の充填性は要求せず、元の評価射自体を扱う。
使われ方：同じ section product scaffold の係数から fiber への同値比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {I : Type u} [Category.{u} I] {B : SSet.{u}} (F : I ⥤ LeftFibrationObject B)

instance strictLeftTransportSectionDiagram_kan (v : I × TransportSimplexCategory B) :
    KanComplex ((strictLeftTransportSectionDiagram F ⋙ kanObjectForget).obj v) :=
  inferInstanceAs (KanComplex ((strictLeftTransportSectionDiagram F).obj v).obj)

/-- 同じ単体の同じ初頂点での評価は trivial Kan fibration。 -/
lemma sectionProductValueEvaluation_trivialKanFibration (i : I) (s : TransportSimplexCategory B) :
    TrivialKanFibration (sectionProductValueEvaluation F i s) := by
  have h := relativeFunctorEvaluate_trivialKanFibration_of_pointMap (F.obj i).val.hom
    (SSet.yonedaEquiv.symm s.objDown.val) (scaffoldFirstVertex s.objDown.obj.unop.len)
    (scaffoldFirstVertex_leftAnodyne _)
  have hv : (scaffoldFirstVertex s.objDown.obj.unop.len).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 0) = stdSimplex.obj₀Equiv.symm (0 : Fin _) := by
    rw [scaffoldFirstVertex, SSet.yonedaEquiv_symm_zero]
    change PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin _)) 0 = _
    exact PinchedHom.constant_zero _
  rw [hv] at h
  exact h

/-- 元の指定値への同じ評価射自体は ∞ 同値。 -/
lemma sectionProductValueEvaluation_isQCatEquivalence (i : I) (s : TransportSimplexCategory B) :
    IsQCatEquivalence (sectionProductValueEvaluation F i s) := by
  have := sectionProductValueEvaluation_trivialKanFibration F i s
  exact isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.F2.Ind
