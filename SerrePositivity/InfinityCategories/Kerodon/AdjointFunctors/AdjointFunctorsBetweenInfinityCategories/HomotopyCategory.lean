module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PointConstantHomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantObjectNaturality
public import Mathlib.Tactic.CrossRefAttribute
/-!
概要：実 ∞ 随伴を、同じ二関手の通常のホモトピー圏の随伴へ移す。
方針：一点上の全パラメータ Hom 対応を評価し、同じ左随伴の右随伴の一意性を使う。
規約：全ての射への自然性と、単位・余単位との整合を保持する。
使われ方：一般 kernel の実 RHom と既存の主導来 RHom の照合。

対応節は Kerodon 6.2（Tag 02EH）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 実 ∞ 随伴から、指定頂点のホモトピー圏の Hom 全単射を得る。 -/
def QCatAdjunction.hoVertexHomEquiv {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    ((HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) x) : hoFunctor.obj Y) ⟶
      HomotopyCategory.mk y) ≃
      ((HomotopyCategory.mk x : hoFunctor.obj X) ⟶
        HomotopyCategory.mk (G.app (Opposite.op ⦋0⦌) y)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointConstantHomEquiv Y (F.app (Opposite.op ⦋0⦌) x) y).trans
    ((a.constantHomEquiv (Δ[0] : SSet.{u}) x y).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointConstantHomEquiv X x (G.app (Opposite.op ⦋0⦌) y)).symm)

/-- ホモトピー圏の Hom 対応は、元の全関手の定値 Hom 対応を表す。 -/
lemma QCatAdjunction.hoVertexHomEquiv_spec {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (α : (HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) x) : hoFunctor.obj Y) ⟶
      HomotopyCategory.mk y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointConstantHomEquiv X x (G.app (Opposite.op ⦋0⦌) y)
      (a.hoVertexHomEquiv x y α) = a.constantHomEquiv (Δ[0] : SSet.{u}) x y
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointConstantHomEquiv Y (F.app (Opposite.op ⦋0⦌) x) y α) := by
  simp only [hoVertexHomEquiv, Equiv.trans_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointConstantHomEquiv X x (G.app (Opposite.op ⦋0⦌) y)).apply_symm_apply _

/-- 元のホモトピー圏の Hom 対応は、終域の全ての射への後合成に自然。 -/
lemma QCatAdjunction.hoVertexHomEquiv_naturality_right {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    {x : X _⦋0⦌} {y y' : Y _⦋0⦌}
    (α : (HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) x) : hoFunctor.obj Y) ⟶
      HomotopyCategory.mk y)
    (δ : (HomotopyCategory.mk y : hoFunctor.obj Y) ⟶ HomotopyCategory.mk y') :
    a.hoVertexHomEquiv x y' (α ≫ δ) =
      a.hoVertexHomEquiv x y α ≫ (hoFunctor.map G).toFunctor.map δ := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointConstantHomEquiv X x (G.app (Opposite.op ⦋0⦌) y')).injective
  rw [a.hoVertexHomEquiv_spec]
  have hc := a.hoVertexHomEquiv_spec x y α
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointConstantHomEquiv_apply] at hc ⊢
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp]
  rw [hc]
  exact a.constantHomEquiv_naturality_right x (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap _ α) δ

/-- 元のホモトピー圏の Hom 対応は、始域の全ての射への前合成に自然。 -/
lemma QCatAdjunction.hoVertexHomEquiv_naturality_left {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    {x' x : X _⦋0⦌} {y : Y _⦋0⦌}
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x)
    (α : (HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) x) : hoFunctor.obj Y) ⟶
      HomotopyCategory.mk y) :
    a.hoVertexHomEquiv x' y ((hoFunctor.map F).toFunctor.map γ ≫ α) =
      γ ≫ a.hoVertexHomEquiv x y α := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointConstantHomEquiv X x' (G.app (Opposite.op ⦋0⦌) y)).injective
  rw [a.hoVertexHomEquiv_spec]
  have hc := a.hoVertexHomEquiv_spec x y α
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointConstantHomEquiv_apply] at hc ⊢
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp]
  rw [hc]
  exact a.constantHomEquiv_naturality_left y γ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap _ α)

/-- 同じ実二関手の通常の h 上の Hom 全単射。 -/
@[kerodon 02EZ]
def QCatAdjunction.hoHomEquiv {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    (x : hoFunctor.obj X) (y : hoFunctor.obj Y) :
    ((hoFunctor.map F).toFunctor.obj x ⟶ y) ≃ (x ⟶ (hoFunctor.map G).toFunctor.obj y) :=
  a.hoVertexHomEquiv x.as.as y.as.as

/-- 実 ∞ 随伴から得る、同じ二関手の通常の h 上の随伴。 -/
@[kerodon 02EZ]
def QCatAdjunction.toHoAdjunction {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) :
    (hoFunctor.map F).toFunctor ⊣ (hoFunctor.map G).toFunctor :=
  Adjunction.mkOfHomEquiv {
    homEquiv := a.hoHomEquiv
    homEquiv_naturality_right := by
      intro x y y' f g
      exact a.hoVertexHomEquiv_naturality_right f g
    homEquiv_naturality_left_symm := by
      intro x' x y f g
      apply (a.hoVertexHomEquiv x'.as.as y.as.as).injective
      change (a.hoVertexHomEquiv x'.as.as y.as.as)
        ((a.hoVertexHomEquiv x'.as.as y.as.as).symm (f ≫ g)) =
          (a.hoVertexHomEquiv x'.as.as y.as.as)
            ((hoFunctor.map F).toFunctor.map f ≫ (a.hoVertexHomEquiv x.as.as y.as.as).symm g)
      rw [Equiv.apply_symm_apply, a.hoVertexHomEquiv_naturality_left, Equiv.apply_symm_apply] }
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
