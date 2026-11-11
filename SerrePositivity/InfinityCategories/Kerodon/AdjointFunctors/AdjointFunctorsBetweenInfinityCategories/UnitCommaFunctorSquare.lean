module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaSquares
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.DegenerateFunctorHomSquare
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber

/-!
概要：comma の正方形を関手単体集合の正方形として読み、合成関係を得る。
方針：二つの区間をパラメータ A の後に並べて curry し、四辺を比較する。
規約：パラメータ A と X,Y の quasicategory 性は不要。
使われ方：単位比較の導来 fiber への射の coherence を供給する。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：パラメータを二つの区間の前から間へ移す。
方針：結合子の逆と第一・第二因子の交換を使う。
規約：出力は (射の区間×A)×ホモトピーの区間。
使われ方：comma の正方形の curry。 -/
def commaSquareReorder (A : SSet.{u}) :
    A ⊗ ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⟶ ((Δ[1] : SSet.{u}) ⊗ A) ⊗ Δ[1] :=
  (α_ A Δ[1] Δ[1]).inv ≫ ((β_ A (Δ[1] : SSet.{u})).hom ▷ Δ[1])

/-- 概要：comma の正方形の上辺が表す X 値のホモトピー。
方針：Y の区間図式を G で後合成する。
規約：端点は指定した二頂点の標的。
使われ方：単位の左辺との h Fun での合成。 -/
noncomputable def UnitCommaFiberSquare.targetHomotopy {X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget (SSet.const v : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) ≫ G)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget (SSet.const w : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) ≫ G) where
  h := (β_ A (Δ[1] : SSet.{u})).hom ≫ s.target ≫ G
  h₀ := by
    rw [← Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ s.target ≫ G = _
    rw [← Category.assoc, s.target_zero]
    rfl
  h₁ := by
    rw [← Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ s.target ≫ G = _
    rw [← Category.assoc, s.target_one]
    rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：comma の coherence を Fun(A,X) の正方形へ移す。
方針：パラメータを前に移して curry する。
規約：第一座標が Y の射、第二座標が x からの矢印の時間。
使われ方：二つの三角形による合成関係。 -/
noncomputable def UnitCommaFiberSquare.functorSquare {X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom A).obj X :=
  curry (commaSquareReorder A ≫ s.coherence.h)

/-- 概要：関手正方形の下辺は x の定値関手の恒等辺。
方針：coherence の時間零の条件を curry する。
規約：非可逆な coherence でも成立する。
使われ方：四辺の合成関係の退化辺の消去。 -/
lemma UnitCommaFiberSquare.functorSquare_bottom {X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A) :
    SSet.ι₀ ≫ s.functorSquare = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X)) := by
  apply uncurry_injective
  rw [uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  simp only [UnitCommaFiberSquare.functorSquare, uncurry_curry]
  have hc : A ◁ (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
      commaSquareReorder A = (β_ A (Δ[1] : SSet.{u})).hom ≫ SSet.ι₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, hc, Category.assoc, s.coherence.h₀]
  change (β_ A (Δ[1] : SSet.{u})).hom ≫ SSet.const x = fst A Δ[1] ≫ SSet.const x
  rw [SSet.comp_const, SSet.comp_const]

/-- 概要：関手正方形の上辺は G で後合成した標的のホモトピー。
方針：coherence の時間一の条件を使う。
規約：指定した標的図式をそのまま使う。
使われ方：単位比較の後合成との照合。 -/
lemma UnitCommaFiberSquare.functorSquare_top {X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A) :
    SSet.ι₁ ≫ s.functorSquare = curry s.targetHomotopy.h := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [UnitCommaFiberSquare.functorSquare, uncurry_curry]
  have hc : A ◁ (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
      commaSquareReorder A = (β_ A (Δ[1] : SSet.{u})).hom ≫ SSet.ι₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, hc, Category.assoc, s.coherence.h₁]
  rfl

/-- 概要：関手正方形の左辺は v が表す x からの矢印の定値族。
方針：coherence の零側辺の条件を curry する。
規約：ホモトピーの代表の厳密な等式。
使われ方：単位成分の認識。 -/
lemma UnitCommaFiberSquare.functorSquare_left {X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ s.functorSquare =
      curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const v : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)).h := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [UnitCommaFiberSquare.functorSquare, uncurry_curry]
  have hc : A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ commaSquareReorder A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ▷ (Δ[1] : SSet.{u}) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, hc, s.coherence_zero]

/-- 概要：関手正方形の右辺は w が表す x からの矢印の定値族。
方針：coherence の一側辺の条件を curry する。
規約：ホモトピーの代表の厳密な等式。
使われ方：導来 fiber の指定点を認識する。 -/
lemma UnitCommaFiberSquare.functorSquare_right {X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ s.functorSquare =
      curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const w : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)).h := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [UnitCommaFiberSquare.functorSquare, uncurry_curry]
  have hc : A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ commaSquareReorder A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ▷ (Δ[1] : SSet.{u}) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, hc, s.coherence_one]

/-- 概要：comma の左辺の後に G の標的辺を合成すると右辺になる。
方針：関手正方形の四辺の式から h Fun の合成関係を得る。
規約：X や Y の quasicategory 性はこの合成関係には不要。
使われ方：単位比較の導来 fiber に入るホモトピーの構成。 -/
lemma UnitCommaFiberSquare.hom_comp {X Y : SSet.{u}} {G : Y ⟶ X}
    {x : X _⦋0⦌} {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} {A : SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const v : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x))) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        s.targetHomotopy) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const w : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x))) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHom_comp_eq_of_square _ _ _ s.functorSquare s.functorSquare_bottom
    s.functorSquare_top s.functorSquare_left s.functorSquare_right

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
