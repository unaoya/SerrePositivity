module
public import SerrePositivity.EInfinity.ComplexLimits.DerivedNatTransComponent
public import SerrePositivity.EInfinity.ComplexLimits.DiagramDerivedVertex
/-!
概要：元の通常自然変換の導来成分を同じ成分辺の像へ全 Arrow として比較する。
方針：元の混合宇宙円柱の成分式と評価公式を接続する。
規約：元の自然変換・全図式・同じ成分辺を保持する。
使われ方：元の置換 augmentation の全源同型を同じ通常成分へ回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A] {I : Type (u + 1)} [Category.{u} I]
  {F G : I ⥤ Complex A} (a : F ⟶ G)

/-- 概要：同じ図式頂点の等式輸送は全 Arrow の成分射を保持する。
方針：元の等式による後合成を Arrow の標準則で除去する。
規約：元の図式と値を保持。使われ方：自由源比較の端点表示の照合。 -/
lemma complexDiagramDerivedVertexIso_comp_arrow (H : I ⥤ Complex A) (i : I)
    {z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A).obj (Opposite.op ⦋0⦌)}
    (f : (HomotopyCategory.mk z : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A)) ⟶ HomotopyCategory.mk
      ((nerveMap H ≫ complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))) :
    Arrow.mk (f ≫ (complexDiagramDerivedVertexIso A H i).hom) = Arrow.mk f := by
  dsimp only [complexDiagramDerivedVertexIso]
  rw [eqToIso.hom]
  exact Arrow.arrow_mk_comp_eqToHom f
    (congrArg HomotopyCategory.mk (complexDiagramDerived_vertex A H i))

/-- 概要：元の全導来自然変換の評価は同じ成分辺の導来像。
方針：元の円柱の成分式を全 Arrow に送る。
規約：端点表示を保持。使われ方：全源同型の通常射への回収。 -/
lemma complexOrdinaryDerivedNatTransHom_component_arrow (i : I) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (complexOrdinaryDerivedNatTransHom A a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk (a.app i)).map (complexOrdinaryDerivedSource A)).toTruncated) := by
  rw [complexOrdinaryDerivedNatTransHom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy]
  exact Truncated.HomotopyCategory.congr_arrowMk_homMk _ _
    (complexOrdinaryDerivedNatTransHomotopy_component A a i)

/-- 概要：元の全導来自然同型の順射の評価は同じ成分辺の導来像。
方針：元の同型の順射を同じ自然変換の全二胞体へ戻す。
規約：元の弱成分を選び直さない。使われ方：置換 augmentation の源比較。 -/
lemma complexOrdinaryDerivedNatTransIso_component_arrow
    (ha : ∀ i, QuasiIso (a.app i)) (i : I) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (complexOrdinaryDerivedNatTransIso A a ha).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk (a.app i)).map (complexOrdinaryDerivedSource A)).toTruncated) := by
  change Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (complexOrdinaryDerivedNatTransHom A a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) = _
  exact complexOrdinaryDerivedNatTransHom_component_arrow A a i

end SerrePositivity.EInfinity.ComplexLimits
