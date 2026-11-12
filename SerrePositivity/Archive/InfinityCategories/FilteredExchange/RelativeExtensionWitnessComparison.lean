module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionEndpoint

/-!
概要：既存の具体的終点比較を元の二延長の同じ指定同型の像として表示する。
方針：実際の終点頂点の表示を揃える移送だけを除く。
規約：指定同型を再選択しない。使われ方：元の三角形比較の fiber 制限への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 具体的終点比較は、元の二つの実延長の指定同型を元の終点評価で写したもの。 -/
lemma relativeExtensionEndpoint_witnessIso_heq_map {A D C E F B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (d : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ d)
    (j : C ⟶ A) (q : F ⟶ B) (a : C ⟶ F) (hj : j ≫ d = a ≫ q)
    (W W' : A ⟶ E) (hW : W ≫ p = d) (hW' : W' ≫ p = d)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
    (g g' : C ⟶ pullback p q) (hg : g ≫ pullback.snd p q = a)
    (hg' : g' ≫ pullback.snd p q = a)
    (hWj : j ≫ W = g ≫ pullback.fst p q) (hWj' : j ≫ W' = g' ≫ pullback.fst p q) :
    HEq (relativeFunctorExtensionEndpoint_witnessIso p d i hi v hv j q a hj
      W W' hW hW' hWi hWi' g g' hg hg' hWj hWj')
      (VertexIso.map
        ((relativeFunctorExtensionSpace_isContractibleKan p d i hi v hv).vertexIso
          (relativeFunctorExtensionSpaceVertexEquiv p d i v hv ⟨W, hW, hWi⟩)
          (relativeFunctorExtensionSpaceVertexEquiv p d i v hv ⟨W', hW', hWi'⟩))
        (relativeFunctorExtensionEndpoint p d i v hv j q a hj)) := by
  unfold relativeFunctorExtensionEndpoint_witnessIso
  exact iso_endpoints_heq _ _ _

end SerrePositivity.InfinityCategories.F2
