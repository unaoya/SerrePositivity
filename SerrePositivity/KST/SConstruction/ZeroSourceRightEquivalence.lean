module
public import SerrePositivity.KST.SConstruction.ZeroSourceTheta
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroCofiberIso

/-! # 零 subobject の cofiber 図式の右辺の可逆性
概要：θ が持ち上げる元の右辺は全頂点で可逆である。
方針：左側の両頂点が始対象である押し出しの右辺の同型判定を使う。
規約：指定した右辺そのものの可逆性。使われ方：θ の gapped 性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：内部 Hom の族を頂点で制限して uncurry すると、その頂点が表す元の関手。
方針：curry の頂点公式と二つの逆律。
規約：形状とパラメーターは任意。使われ方：右辺の族の実際の辺の同定。 -/
lemma uncurry_vertex_restriction {A B C : SSet.{u}} (F : B ⟶ (ihom A).obj C) (b : B _⦋0⦌) :
    lift (𝟙 A) (SSet.const b) ≫ uncurry F =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C).symm (F.app (Opposite.op ⦋0⦌) b) := by
  have h := curry_vertex_value (uncurry F) b
  rw [curry_uncurry] at h
  rw [h]
  change _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C) _)
  rw [Equiv.symm_apply_apply]

/-- 概要：固定零 subobject の右辺の族を頂点で制限すると元の正方形の右辺。
方針：uncurry の頂点制限と内部 Hom の前合成の式。
規約：実際の射の等号。使われ方：元の右辺の可逆性の照合。 -/
lemma zeroSourceCofibersRightPrism_vertex {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C)
    (b : (zeroSourceCofibers z) _⦋0⦌) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const b) ≫ zeroSourceCofibersRightPrism z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι).app (Opposite.op ⦋0⦌)
          ((zeroSourceCofibersι z).app (Opposite.op ⦋0⦌) b)) := by
  rw [zeroSourceCofibersRightPrism, uncurry_vertex_restriction]
  exact functorVertexEquiv_symm_pre _ _

/-- 概要：固定零 subobject の cofiber 図式の右辺は h C の同型。
方針：subobject は指定零対象、左上角も零対象なので押し出しの右辺の判定を使う。
規約：元の右辺の同型性。使われ方：θ の点ごとの可逆性。 -/
lemma zeroSourceCofibersRight_isIso {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C)
    (b : (zeroSourceCofibers z) _⦋0⦌) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι).app (Opposite.op ⦋0⦌)
        ((zeroSourceCofibersι z).app (Opposite.op ⦋0⦌) b)))) := by
  let v := (zeroSourceCofibersι z).app (Opposite.op ⦋0⦌) b
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
  have hs := ConcreteCategory.congr_hom (NatTrans.congr_app
    (zeroSourceCofibersι_source z) (Opposite.op ⦋0⦌)) b
  have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val) 0 0 = z.vertex := by
    have he : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val) 0 0 =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm 0)).app
            (Opposite.op ⦋0⦌) v.val := functorVertexEquiv_symm_evaluate _ _
    rw [he]
    change (cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) v = z.vertex
    change (cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) v =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z.vertex 0 at hs
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at hs
    exact hs
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isIso_squareHoRight_of_pushout_initial_left _ hv.2 (hz.symm ▸ z.isInitial) hv.1.1

/-- 概要：右辺の prism の各頂点での辺は可逆。
方針：頂点制限を元の右辺に同定し、そのホモトピー類の同型性を使う。
規約：指定された辺そのものの可逆性。使われ方：固定始点の矢印への反映。 -/
lemma zeroSourceCofibersRightPrism_isInvertible {C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (b : (zeroSourceCofibers z) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((zeroSourceCofibersRightPrism z).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1))) := by
  let R := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι).app (Opposite.op ⦋0⦌)
      ((zeroSourceCofibersι z).app (Opposite.op ⦋0⦌) b))
  have he := congrArg SSet.yonedaEquiv (zeroSourceCofibersRightPrism_vertex z b)
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  rw [SSet.yonedaEquiv_comp] at he
  change (zeroSourceCofibersRightPrism z).app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1) =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ R) at he
  rw [← hi] at he
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge] at he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).2
  exact zeroSourceCofibersRight_isIso z b

end SerrePositivity.KST.SConstruction
