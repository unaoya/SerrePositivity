module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingSpace

/-!
概要：写像空間のパラメータ族を、定値関手間の辺として表示する。
方針：両端固定の区間模型の普遍性と内部 Hom の閉構造を使う。
規約：straightening を使わず、標的の quasicategory 性もこの表示には不要。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1）、HTT §5.2 のパラメータ付き adjunct 対応。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：定値端点の境界図式と区間模型の指定境界は一致する。
方針：次数ごとの二つの分岐を比較する。
規約：パラメータ A の値は使わない。
使われ方：straightening を含む集約を経由せず区間模型の端点を使う。 -/
lemma intervalFamily_boundary {A X : SSet.{u}} (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (SSet.const x : A ⟶ X) (SSet.const y) =
      fst (boundary 1 : SSet.{u}) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：区間写像空間の族の零端点は始点に定値。
方針：指定境界の式を零端点へ制限する。
規約：任意のパラメータ A。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の定値関手の表示。 -/
lemma intervalFamily_zero {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f = SSet.const x := by
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 A ≫
        ((boundary 1).ι ▷ A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f := by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι]
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_boundary, ← intervalFamily_boundary,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero]

/-- 概要：区間写像空間の族の一端点は終点に定値。
方針：指定境界の式を一端点へ制限する。
規約：任意のパラメータ A。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の定値関手の表示。 -/
lemma intervalFamily_one {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f = SSet.const y := by
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 A ≫
        ((boundary 1).ι ▷ A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f := by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι]
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_boundary, ← intervalFamily_boundary,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one]

/-- 概要：両端を固定した区間の族を写像空間へ戻す。
方針：端点条件から境界条件を復元して curry する。
規約：区間を第一因子に置く。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） のパラメータ付き表示。 -/
noncomputable def intervalFamilyCurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = SSet.const x)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = SSet.const y) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurry H (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict, h₀, h₁, intervalFamily_boundary])

/-- 概要：端点を指定して curry した族の展開は元の族。
方針：区間模型の普遍性の往復を使う。
規約：端点条件の証明には依存しない。
使われ方：写像空間の族と関手の辺の両逆の計算。 -/
lemma intervalFamilyUncurry_curry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = SSet.const x)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = SSet.const y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (intervalFamilyCurry H h₀ h₁) = H :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curry _ _


/-- 概要：区間写像空間の族は定値関手を結ぶホモトピーを与える。
方針：族を展開して区間とパラメータの順序を交換する。
規約：任意の単体集合 A をパラメータに取る。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の定値関手間の Hom の表示。 -/
noncomputable def intervalFamilyHomotopy {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    SSet.Homotopy (SSet.const x : A ⟶ X) (SSet.const y) where
  h := (β_ A (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f
  h₀ := by
    rw [← Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f = _
    exact intervalFamily_zero f
  h₁ := by
    rw [← Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f = _
    exact intervalFamily_one f
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：区間写像空間の族を定値関手間の辺に移す。
方針：ホモトピーを curry して関手単体集合の一次単体にする。
規約：ここでは h Fun の類への商を取らない。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） のパラメータ付き対応。 -/
noncomputable def intervalFamilyEdge {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (intervalFamilyHomotopy f)

/-- 概要：定値関手間の辺を区間写像空間の族として表示する。
方針：辺を uncurry し、区間を第一因子に戻して両端固定の普遍性を使う。
規約：辺は任意。標的の quasicategory 性は不要。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） のパラメータ付き対応の逆。 -/
noncomputable def intervalFamilyOfEdge {A X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y))) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y :=
  intervalFamilyCurry
    ((β_ (Δ[1] : SSet.{u}) A).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e).h)
    (by
      rw [← Category.assoc]
      change SSet.ι₀ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e).h = _
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e).h₀)
    (by
      rw [← Category.assoc]
      change SSet.ι₁ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e).h = _
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e).h₁)

/-- 概要：族を関手の辺に移して戻すと元の族。
方針：uncurry の単射性と閉構造の両逆、対称性を使う。
規約：任意のパラメータ A。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の族の表示の往復。 -/
lemma intervalFamilyOfEdge_edge {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    intervalFamilyOfEdge (intervalFamilyEdge f) = f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective x y
  simp [intervalFamilyOfEdge, intervalFamilyEdge, intervalFamilyHomotopy,
    intervalFamilyUncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge]

/-- 概要：関手の辺を族に移して戻すと元の辺。
方針：一次単体を比較し、curry と uncurry の両逆を使う。
規約：辺の端点の証明は proof irrelevance で同一視する。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の族の表示の逆の往復。 -/
lemma intervalFamilyEdge_ofEdge {A X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y))) :
    intervalFamilyEdge (intervalFamilyOfEdge e) = e := by
  apply SSet.Truncated.Edge.ext
  simp [intervalFamilyEdge, intervalFamilyHomotopy, intervalFamilyOfEdge,
    intervalFamilyUncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge]

/-- 概要：区間写像空間の族と定値関手間の辺の厳密な全単射。
方針：二つの変換と両逆の計算を束ねる。
規約：商を取る前の辺の全単射。ホモトピー類の全単射は別途証明する。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の族による表示。 -/
noncomputable def intervalFamilyEdgeEquiv (A X : SSet.{u}) (x y : X _⦋0⦌) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) ≃
      SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y)) where
  toFun := intervalFamilyEdge
  invFun := intervalFamilyOfEdge
  left_inv := intervalFamilyOfEdge_edge
  right_inv := intervalFamilyEdge_ofEdge

/-- 概要：区間写像空間の族が定める h Fun の射。
方針：対応する関手の辺の homMk を取る。
規約：パラメータ A に quasicategory 性は不要。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） のパラメータ付き adjunct の始域。 -/
noncomputable def intervalFamilyHom {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X)) :
      hoFunctor.obj ((ihom A).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y)) :=
  SSet.Truncated.HomotopyCategory.homMk (intervalFamilyEdge f)

/-- 概要：定値関手間の h Fun の射は区間模型の族で表せる。
方針：quasicategory の射を辺で表し、辺と族の全単射を使う。
規約：標的 X の quasicategory 性だけを要求する。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の普遍的な族に adjunct を適用する準備。 -/
lemma intervalFamilyHom_surjective (A X : SSet.{u}) [Quasicategory X] (x y : X _⦋0⦌) :
    Function.Surjective (intervalFamilyHom (A := A) (X := X) (x := x) (y := y)) := by
  intro α
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y)) α
  refine ⟨intervalFamilyOfEdge e, ?_⟩
  simpa only [intervalFamilyHom, intervalFamilyEdge_ofEdge] using he

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
