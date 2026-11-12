module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorCurryHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.IsoEndpointNormalization

/-!
概要：始点固定の延長の指定比較を、任意の部分図式上の切断族の同型へ写す。
方針：同じ延長の包含・底上の制限・相対 curry の豊穣作用を一つの写像として合成する。
規約：指定比較の値を保持。使われ方：native 全三角形と元の fiber の二脚の同時比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {A D C L E B : SSet.{u}} (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A)
  (v : D ⟶ E) (hv : v ≫ p = i ≫ b) (j : C ⊗ L ⟶ A) (a : C ⟶ B)
  (hj : j ≫ b = fst C L ≫ a)

/-- 全延長を同じ部分図式上の切断の全パラメータ族へ送る実際の写像。 -/
def relativeExtensionCurryRestriction :
    relativeFunctorExtensionSpace p b i v hv ⟶ (ihom L).obj (relativeFunctorSpace p a) :=
  relativeFunctorExtensionSpaceι p b i v hv ≫
    relativeFunctorOverPre p (Over.homMk (U := Over.mk (fst C L ≫ a)) (V := Over.mk b) j hj) ≫
      relativeFunctorCurryHom p a L

/-- 具体的な延長の像は、その同じ部分図式への制限を相対 curry した関手頂点。 -/
lemma relativeExtensionCurryRestriction_vertex (W : A ⟶ E) (hW : W ≫ p = b)
    (hWi : i ≫ W = v) :
    (relativeExtensionCurryRestriction p b i v hv j a hj).app _
      (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W, hW, hWi⟩) =
      functorVertex (relativeFunctorCurry (p := p) (a := a) (j ≫ W)
        (by rw [Category.assoc, hW, hj])) := by
  exact (congrArg (fun z => (relativeFunctorCurryHom p a L).app _ z)
    (relativeFunctorOverPre_vertex p
      (Over.homMk (U := Over.mk (fst C L ≫ a)) (V := Over.mk b) j hj) W hW)).trans
        (relativeFunctorCurryHom_vertex p a (j ≫ W) (by rw [Category.assoc, hW, hj]))

variable (W W' : A ⟶ E) (hW : W ≫ p = b) (hW' : W' ≫ p = b)
  (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
  (e : VertexIso
    (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W, hW, hWi⟩)
    (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W', hW', hWi'⟩))

/-- 指定延長比較の像を、元の制限した切断族の関手同型として表示する。 -/
def relativeExtensionCurryRestrictionIso :
    FunctorIso
      (relativeFunctorCurry (p := p) (a := a) (j ≫ W) (by rw [Category.assoc, hW, hj]))
      (relativeFunctorCurry (p := p) (a := a) (j ≫ W') (by rw [Category.assoc, hW', hj])) :=
  isoNormalizeEndpoints (VertexIso.map e (relativeExtensionCurryRestriction p b i v hv j a hj))
    (congrArg SSet.HomotopyCategory.mk
      (relativeExtensionCurryRestriction_vertex p b i v hv j a hj W hW hWi))
    (congrArg SSet.HomotopyCategory.mk
      (relativeExtensionCurryRestriction_vertex p b i v hv j a hj W' hW' hWi'))

end SerrePositivity.InfinityCategories.F2
