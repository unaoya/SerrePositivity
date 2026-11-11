module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionCurryRestriction
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality

/-!
概要：切断族の指定比較の後合成を、元の全延長比較の単一の指定像として表示する。
方針：関手同型の後合成と端点補正の関手性を使い、同じ豊穣作用の合成へ戻す。
規約：明示した端点の表示以外を変えない。使われ方：native 最終 fiber 同型の指定像表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 切断族の指定像を後合成しても、同じ全延長比較の単一の指定像を保持する。 -/
lemma relativeExtensionCurryRestrictionIso_postcomp_heq_map {A D C L E B Z : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⊗ L ⟶ A) (a : C ⟶ B) (hj : j ≫ b = fst C L ≫ a)
    (W W' : A ⟶ E) (hW : W ≫ p = b) (hW' : W' ≫ p = b)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
    (e : VertexIso
      (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W, hW, hWi⟩)
      (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W', hW', hWi'⟩))
    (q : relativeFunctorSpace p a ⟶ Z) :
    HEq ((relativeExtensionCurryRestrictionIso p b i v hv j a hj
      W W' hW hW' hWi hWi' e).postcomp q)
      (VertexIso.map e (relativeExtensionCurryRestriction p b i v hv j a hj ≫
        (ihom L).map q)) := by
  unfold relativeExtensionCurryRestrictionIso
  rw [functorIso_postcomp_eq_mapIso]
  exact (isoNormalizeEndpoints_map_heq (SSet.mapHomotopyCategory ((ihom L).map q)) _ _ _).trans
    (heq_of_eq (vertexIso_map_comp e _ _))

/-- 後合成を含む単一の出力写像は、元の実延長の同じ切断族の関手頂点を保持する。 -/
lemma relativeExtensionCurryRestriction_postcomp_vertex {A D C L E B Z : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⊗ L ⟶ A) (a : C ⟶ B) (hj : j ≫ b = fst C L ≫ a)
    (W : A ⟶ E) (hW : W ≫ p = b) (hWi : i ≫ W = v)
    (q : relativeFunctorSpace p a ⟶ Z) :
    (relativeExtensionCurryRestriction p b i v hv j a hj ≫ (ihom L).map q).app _
      (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W, hW, hWi⟩) =
      functorVertex (relativeFunctorCurry (p := p) (a := a) (j ≫ W)
        (by rw [Category.assoc, hW, hj]) ≫ q) := by
  exact congrArg (fun z => ((ihom L).map q).app _ z)
    (relativeExtensionCurryRestriction_vertex p b i v hv j a hj W hW hWi)

end SerrePositivity.InfinityCategories.F2
