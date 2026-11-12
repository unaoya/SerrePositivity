module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PrismCylinderEndpoint
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses

/-!
概要：指定済みの prism 比較円柱を係数の射で制限し、底・初期値と終点の類を保つ。
方針：同じ円柱を前合成して標準 prism の係数を揃え、終点の raw な射を照合する。
規約：係数に Kan 性を要求しない。使われ方：三角形全体の比較を実際の頂点へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 指定した同じ prism の係数だけを引き戻す。 -/
def prismParameterPrecomp {A C E : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (u : C ⟶ A) : (Δ[1] : SSet.{u}) ⊗ C ⟶ E :=
  (Δ[1] ◁ u) ≫ H

variable {A C E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  {a b : B _⦋0⦌} (e : B.Edge a b) (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)
  (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
  (hH₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a)
  (hHp : H ≫ p = fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge)
  (D : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PrismTransportCylinder p e f H) (u : C ⟶ A)

/-- 標準 prism の係数変更は、同じ標準輸送の prism を厳密に引き戻す。 -/
lemma prismTransportStandard_parameter :
    (Δ[1] ◁ u) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard p e f = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard p e (u ≫ f) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard, MonoidalCategory.whiskerLeft_comp, Category.assoc]

include hH₀ in
omit [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] in
/-- 係数変更後の初期値は、同じ元の初期族の制限。 -/
lemma prismParameterPrecomp_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 C ≫ prismParameterPrecomp H u = (u ≫ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a := by
  rw [prismParameterPrecomp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
    hH₀, Category.assoc]

include hHp in
omit [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] in
/-- 係数変更後も元の底の辺を厳密に被覆する。 -/
lemma prismParameterPrecomp_projection :
    prismParameterPrecomp H u ≫ p =
      fst (Δ[1] : SSet.{u}) C ≫ SSet.yonedaEquiv.symm e.edge := by
  rw [prismParameterPrecomp, Category.assoc, hHp, ← Category.assoc, whiskerLeft_fst]

/-- 同じ比較円柱を係数で前合成し、底と初期値を同時に保つデータとして保持する。 -/
def prismCylinderParameter : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PrismTransportCylinder p e (u ≫ f) (prismParameterPrecomp H u) := by
  let K := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp D.homotopy (Δ[1] ◁ u)
  refine
    { homotopy :=
        { h := K.h
          h₀ := K.h₀
          h₁ := K.h₁.trans (prismTransportStandard_parameter p e f u)
          rel := by
            apply SSet.hom_ext
            intro n
            apply ConcreteCategory.hom_ext
            intro z
            exact False.elim z.1.property }
      projection := ?_
      initial := ?_ }
  · change (((Δ[1] ◁ u) ▷ (Δ[1] : SSet.{u})) ≫ D.homotopy.h) ≫ p = _
    rw [Category.assoc, D.projection, ← Category.assoc, whiskerRight_fst,
      Category.assoc, ← Category.assoc (Δ[1] ◁ u), whiskerLeft_fst]
  · change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ C) ▷ (Δ[1] : SSet.{u})) ≫
      (((Δ[1] ◁ u) ▷ (Δ[1] : SSet.{u})) ≫ D.homotopy.h) = _
    have hx : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ C) ▷ (Δ[1] : SSet.{u})) ≫
        ((Δ[1] ◁ u) ▷ (Δ[1] : SSet.{u})) =
        ((Δ[0] ◁ u) ▷ (Δ[1] : SSet.{u})) ≫
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ A) ▷ (Δ[1] : SSet.{u})) := by
      rw [← MonoidalCategory.comp_whiskerRight, ← MonoidalCategory.whisker_exchange,
        MonoidalCategory.comp_whiskerRight]
    rw [← Category.assoc, hx, Category.assoc, D.initial,
      ← Category.assoc, whiskerRight_fst, Category.assoc,
      ← Category.assoc (Δ[0] ◁ u), whiskerLeft_snd]
    simp only [Category.assoc]

variable (g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) (hH₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)

include hH₁ in
omit [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] in
/-- 終点族も、同じ元の終点族の係数変更そのもの。 -/
lemma prismParameterPrecomp_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 C ≫ prismParameterPrecomp H u = (u ≫ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b := by
  rw [prismParameterPrecomp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
    hH₁, Category.assoc]

/-- 制限した円柱の終点比較は、元の終点比較を前合成した同じ raw な射を持つ。 -/
lemma prismCylinderEndpointHomotopy_parameter_raw :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismCylinderEndpointHomotopy p e (u ≫ f) (prismParameterPrecomp H u)
      (prismCylinderParameter p e f H D u) (u ≫ g)
      (prismParameterPrecomp_one p H u g hH₁)).h =
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismCylinderEndpointHomotopy p e f H D g hH₁) u).h := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismCylinderEndpointHomotopy_projection]
  change _ = ((u ▷ (Δ[1] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismCylinderEndpointHomotopy p e f H D g hH₁).h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismCylinderEndpointHomotopy_projection]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 C ▷ (Δ[1] : SSet.{u})) ≫
      (((Δ[1] ◁ u) ▷ (Δ[1] : SSet.{u})) ≫ D.homotopy.h) = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
    MonoidalCategory.comp_whiskerRight, Category.assoc]

/-- 係数変更後の輸送比較同型の射は、元の同型を同じ係数で前合成した射と一致する。 -/
lemma prismTransportIso_parameter_hom_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.leftFibrationPrism_transportIso p e (u ≫ f) (u ≫ g) (prismParameterPrecomp H u)
      (prismParameterPrecomp_zero p f H hH₀ u) (prismParameterPrecomp_one p H u g hH₁)
      (prismParameterPrecomp_projection p e H hHp u)).hom =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.leftFibrationPrism_transportIso p e f g H hH₀ hH₁ hHp) u).hom := by
  let D := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportCylinder p e f H hH₀ hHp
  have hC := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismCylinderEndpointHomotopy_hom p e (u ≫ f) (prismParameterPrecomp H u)
    (prismParameterPrecomp_zero p f H hH₀ u) (prismParameterPrecomp_projection p e H hHp u)
    (prismCylinderParameter p e f H D u) (u ≫ g) (prismParameterPrecomp_one p H u g hH₁)
  have hA := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismCylinderEndpointHomotopy_hom p e f H hH₀ hHp D g hH₁
  refine (congrArg Arrow.mk hC).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq _ _
      (prismCylinderEndpointHomotopy_parameter_raw p e f H D u g hH₁)).trans ?_)
  have h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismCylinderEndpointHomotopy p e f H D g hH₁) u)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.leftFibrationPrism_transportIso p e f g H hH₀ hH₁ hHp) u).hom := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom, hA]
    rfl
  exact congrArg Arrow.mk h

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
