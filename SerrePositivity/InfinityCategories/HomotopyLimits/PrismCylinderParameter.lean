module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismCylinderEndpoint
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomotopyClasses

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 指定した同じ prism の係数だけを引き戻す。 -/
def prismParameterPrecomp {A C E : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (u : C ⟶ A) : (Δ[1] : SSet.{u}) ⊗ C ⟶ E :=
  (Δ[1] ◁ u) ≫ H

variable {A C E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  {a b : B _⦋0⦌} (e : B.Edge a b) (f : A ⟶ vertexFiber p a)
  (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
  (hH₀ : prismEndpoint 0 A ≫ H = f ≫ vertexFiberι p a)
  (hHp : H ≫ p = fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge)
  (D : PrismTransportCylinder p e f H) (u : C ⟶ A)

/-- 標準 prism の係数変更は、同じ標準輸送の prism を厳密に引き戻す。 -/
lemma prismTransportStandard_parameter :
    (Δ[1] ◁ u) ≫ prismTransportStandard p e f = prismTransportStandard p e (u ≫ f) := by
  simp only [prismTransportStandard, MonoidalCategory.whiskerLeft_comp, Category.assoc]

include hH₀ in
omit [LeftFibration p] in
/-- 係数変更後の初期値は、同じ元の初期族の制限。 -/
lemma prismParameterPrecomp_zero :
    prismEndpoint 0 C ≫ prismParameterPrecomp H u = (u ≫ f) ≫ vertexFiberι p a := by
  rw [prismParameterPrecomp, ← Category.assoc, prismEndpoint_naturality, Category.assoc,
    hH₀, Category.assoc]

include hHp in
omit [LeftFibration p] in
/-- 係数変更後も元の底の辺を厳密に被覆する。 -/
lemma prismParameterPrecomp_projection :
    prismParameterPrecomp H u ≫ p =
      fst (Δ[1] : SSet.{u}) C ≫ SSet.yonedaEquiv.symm e.edge := by
  rw [prismParameterPrecomp, Category.assoc, hHp, ← Category.assoc, whiskerLeft_fst]

/-- 同じ比較円柱を係数で前合成し、底と初期値を同時に保つデータとして保持する。 -/
def prismCylinderParameter : PrismTransportCylinder p e (u ≫ f) (prismParameterPrecomp H u) := by
  let K := functorHomotopyPrecomp D.homotopy (Δ[1] ◁ u)
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
  · change ((scaffoldFirstVertex 1 ▷ C) ▷ (Δ[1] : SSet.{u})) ≫
      (((Δ[1] ◁ u) ▷ (Δ[1] : SSet.{u})) ≫ D.homotopy.h) = _
    have hx : ((scaffoldFirstVertex 1 ▷ C) ▷ (Δ[1] : SSet.{u})) ≫
        ((Δ[1] ◁ u) ▷ (Δ[1] : SSet.{u})) =
        ((Δ[0] ◁ u) ▷ (Δ[1] : SSet.{u})) ≫
          ((scaffoldFirstVertex 1 ▷ A) ▷ (Δ[1] : SSet.{u})) := by
      rw [← MonoidalCategory.comp_whiskerRight, ← MonoidalCategory.whisker_exchange,
        MonoidalCategory.comp_whiskerRight]
    rw [← Category.assoc, hx, Category.assoc, D.initial,
      ← Category.assoc, whiskerRight_fst, Category.assoc,
      ← Category.assoc (Δ[0] ◁ u), whiskerLeft_snd]
    simp only [Category.assoc]

variable (g : A ⟶ vertexFiber p b) (hH₁ : prismEndpoint 1 A ≫ H = g ≫ vertexFiberι p b)

include hH₁ in
omit [LeftFibration p] in
/-- 終点族も、同じ元の終点族の係数変更そのもの。 -/
lemma prismParameterPrecomp_one :
    prismEndpoint 1 C ≫ prismParameterPrecomp H u = (u ≫ g) ≫ vertexFiberι p b := by
  rw [prismParameterPrecomp, ← Category.assoc, prismEndpoint_naturality, Category.assoc,
    hH₁, Category.assoc]

/-- 制限した円柱の終点比較は、元の終点比較を前合成した同じ raw な射を持つ。 -/
lemma prismCylinderEndpointHomotopy_parameter_raw :
    (prismCylinderEndpointHomotopy p e (u ≫ f) (prismParameterPrecomp H u)
      (prismCylinderParameter p e f H D u) (u ≫ g)
      (prismParameterPrecomp_one p H u g hH₁)).h =
        (functorHomotopyPrecomp (prismCylinderEndpointHomotopy p e f H D g hH₁) u).h := by
  apply vertexFiber_hom_ext p b
  rw [prismCylinderEndpointHomotopy_projection]
  change _ = ((u ▷ (Δ[1] : SSet.{u})) ≫
    (prismCylinderEndpointHomotopy p e f H D g hH₁).h) ≫ vertexFiberι p b
  rw [Category.assoc, prismCylinderEndpointHomotopy_projection]
  change (prismEndpoint 1 C ▷ (Δ[1] : SSet.{u})) ≫
      (((Δ[1] ◁ u) ▷ (Δ[1] : SSet.{u})) ≫ D.homotopy.h) = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, prismEndpoint_naturality,
    MonoidalCategory.comp_whiskerRight, Category.assoc]

/-- 係数変更後の輸送比較同型の射は、元の同型を同じ係数で前合成した射と一致する。 -/
lemma prismTransportIso_parameter_hom_arrow :
    Arrow.mk (leftFibrationPrism_transportIso p e (u ≫ f) (u ≫ g) (prismParameterPrecomp H u)
      (prismParameterPrecomp_zero p f H hH₀ u) (prismParameterPrecomp_one p H u g hH₁)
      (prismParameterPrecomp_projection p e H hHp u)).hom =
      Arrow.mk (FunctorIso.precomp
        (leftFibrationPrism_transportIso p e f g H hH₀ hH₁ hHp) u).hom := by
  let D := prismTransportCylinder p e f H hH₀ hHp
  have hC := prismCylinderEndpointHomotopy_hom p e (u ≫ f) (prismParameterPrecomp H u)
    (prismParameterPrecomp_zero p f H hH₀ u) (prismParameterPrecomp_projection p e H hHp u)
    (prismCylinderParameter p e f H D u) (u ≫ g) (prismParameterPrecomp_one p H u g hH₁)
  have hA := prismCylinderEndpointHomotopy_hom p e f H hH₀ hHp D g hH₁
  refine (congrArg Arrow.mk hC).symm.trans
    ((SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq _ _
      (prismCylinderEndpointHomotopy_parameter_raw p e f H D u g hH₁)).trans ?_)
  have h : SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPrecomp (prismCylinderEndpointHomotopy p e f H D g hH₁) u)) =
      (FunctorIso.precomp (leftFibrationPrism_transportIso p e f g H hH₀ hH₁ hHp) u).hom := by
    rw [functorHomotopyPrecomp_hom, hA]
    rfl
  exact congrArg Arrow.mk h

end
end SerrePositivity.InfinityCategories.HomotopyLimits
