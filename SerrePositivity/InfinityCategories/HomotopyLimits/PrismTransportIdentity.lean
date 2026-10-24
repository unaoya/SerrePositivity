module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismCylinderEndpoint
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomotopyClasses

/-!
概要：標準 prism 自身を入力した輸送比較同型は、同じ終点族の恒等同型となる。
方針：底と初期値を保つ定値円柱を明示し、その終点比較の類を既存の同型へ移す。
規約：単に両端が同じという理由では同型を恒等としない。使われ方：三角形比較の標準側。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  {a b : B _⦋0⦌} (e : B.Edge a b) (f : A ⟶ vertexFiber p a)

/-- 標準 prism 自身の、底と初期値を固定する定値の比較円柱。 -/
def prismTransportIdentityCylinder :
    PrismTransportCylinder p e f (prismTransportStandard p e f) where
  homotopy := functorHomotopyRefl (prismTransportStandard p e f)
  projection := by
    change (fst _ (Δ[1] : SSet.{u}) ≫ prismTransportStandard p e f) ≫ p = _
    rw [Category.assoc, prismTransportStandard_projection]
  initial := by
    change ((scaffoldFirstVertex 1 ▷ A) ▷ (Δ[1] : SSet.{u})) ≫
      (fst _ (Δ[1] : SSet.{u}) ≫ prismTransportStandard p e f) = _
    have h₀ : (scaffoldFirstVertex 1 ▷ A) ≫ prismTransportStandard p e f =
        snd (Δ[0] : SSet.{u}) A ≫ f ≫ vertexFiberι p a := by
      rw [scaffoldFirstVertex_whiskerRight, Category.assoc]
      change snd Δ[0] A ≫ prismEndpoint 0 A ≫ prismTransportStandard p e f = _
      rw [prismTransportStandard_zero]
    rw [← Category.assoc, whiskerRight_fst, Category.assoc, h₀]

/-- 定値比較円柱の終点も、同じ終点族の定値円柱の raw な射である。 -/
lemma prismTransportIdentityEndpoint_raw :
    (prismCylinderEndpointHomotopy p e f (prismTransportStandard p e f)
      (prismTransportIdentityCylinder p e f) (f ≫ edgeTransport p e)
      (prismTransportStandard_one p e f)).h =
        (functorHomotopyRefl (f ≫ edgeTransport p e)).h := by
  apply vertexFiber_hom_ext p b
  rw [prismCylinderEndpointHomotopy_projection]
  change (prismEndpoint 1 A ▷ (Δ[1] : SSet.{u})) ≫
      (fst _ (Δ[1] : SSet.{u}) ≫ prismTransportStandard p e f) =
    (fst _ (Δ[1] : SSet.{u}) ≫ (f ≫ edgeTransport p e)) ≫ vertexFiberι p b
  rw [← Category.assoc, whiskerRight_fst, Category.assoc, prismTransportStandard_one]
  simp only [Category.assoc]

/-- 標準 prism の輸送比較同型の射は、明示した定値円柱により恒等射と一致する。 -/
lemma prismTransportIso_standard_hom :
    (leftFibrationPrism_transportIso p e f (f ≫ edgeTransport p e)
      (prismTransportStandard p e f) (prismTransportStandard_zero p e f)
      (prismTransportStandard_one p e f) (prismTransportStandard_projection p e f)).hom =
        𝟙 (SSet.HomotopyCategory.mk (functorVertex (f ≫ edgeTransport p e))) := by
  have h := prismCylinderEndpointHomotopy_hom p e f (prismTransportStandard p e f)
    (prismTransportStandard_zero p e f) (prismTransportStandard_projection p e f)
    (prismTransportIdentityCylinder p e f) (f ≫ edgeTransport p e)
    (prismTransportStandard_one p e f)
  apply Arrow.mk_injective _ _
  refine (congrArg Arrow.mk h).symm.trans
    ((SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq _ _ (prismTransportIdentityEndpoint_raw p e f)).trans ?_)
  exact congrArg Arrow.mk (functorHomotopyRefl_hom (f ≫ edgeTransport p e))

/-- 標準 prism 自身の比較は、同じ終点図式の恒等同型である。 -/
lemma prismTransportIso_standard :
    leftFibrationPrism_transportIso p e f (f ≫ edgeTransport p e)
      (prismTransportStandard p e f) (prismTransportStandard_zero p e f)
      (prismTransportStandard_one p e f) (prismTransportStandard_projection p e f) =
        Iso.refl (SSet.HomotopyCategory.mk (functorVertex (f ≫ edgeTransport p e))) := by
  apply Iso.ext
  exact prismTransportIso_standard_hom p e f

end
end SerrePositivity.InfinityCategories.HomotopyLimits
