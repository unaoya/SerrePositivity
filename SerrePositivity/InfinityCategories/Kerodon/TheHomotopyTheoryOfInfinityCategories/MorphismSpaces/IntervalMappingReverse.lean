module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFatDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrismOpposite

/-!
概要：区間の両端を固定した写像空間と単体の反転の比較。
方針：パラメーター付き区間族の反転を curry し、二重反転で逆写像則を示す。
規約：始点と終点は交換し、標的とパラメーターも反転する。
使われ方：反転した coherent 合成の底の比較の同値性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：prism の反転は元の族を区別する。
方針：二度反転して二重反転の同型を消去する。
規約：パラメーターと値域の充填性は不要。
使われ方：区間族の反転の逆写像則。 -/
lemma reversePrism_injective {A X : SSet.{u}} :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism (A := A) (Y := X)) := by
  intro H K h
  have hd := congrArg (fun R ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism R ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom) h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_double, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_double] at hd
  apply (cancel_epi (Δ[1] ◁ (SSet.opFunctorCompOpFunctorIso.app A).hom)).1 hd

/-- 概要：端点固定の区間族を反転した端点の区間族へ移す。
方針：prism を反転し、端点の公式で交換した端点を固定して curry する。
規約：パラメーターも反転する。
使われ方：区間写像空間の反転同型の族への作用。 -/
def intervalMappingReverseFamily {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    A.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f))
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_endpoint, show (0 : Fin 2).rev = 1 by decide,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_one]; rfl)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_endpoint, show (1 : Fin 2).rev = 0 by decide,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_zero]; rfl)

/-- 概要：反転した区間族の展開は元の展開の prism の反転。
方針：curry・uncurry の逆写像則を適用する。
規約：全パラメーターを保持する厳密な等式。
使われ方：反転の自然性と逆写像則の計算。 -/
lemma intervalMappingReverseFamily_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (intervalMappingReverseFamily f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints _ _ _

/-- 概要：反転した端点固定の区間族を二重反転の同型で元の向きへ戻す。
方針：もう一度 prism を反転し、標的とパラメーターの二重反転同型を挿入する。
規約：元の二端点を厳密に固定する。
使われ方：反転した区間族の逆写像。 -/
def intervalMappingReverseBack {A X : SSet.{u}} {x y : X _⦋0⦌}
    (g : A.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints
    ((Δ[1] ◁ (SSet.opFunctorCompOpFunctorIso.app A).inv) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g) ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom)
    (by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc]
      change (SSet.opFunctorCompOpFunctorIso.app A).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A.op.op ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g)) ≫
          (SSet.opFunctorCompOpFunctorIso.app X).hom = SSet.const x
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_endpoint, show (0 : Fin 2).rev = 1 by decide,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_one]
      rfl)
    (by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc]
      change (SSet.opFunctorCompOpFunctorIso.app A).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A.op.op ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g)) ≫
          (SSet.opFunctorCompOpFunctorIso.app X).hom = SSet.const y
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_endpoint, show (1 : Fin 2).rev = 0 by decide,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_zero]
      rfl)


/-- 概要：反転を戻す族の展開の式。
方針：curry・uncurry の逆写像則を適用する。
規約：二重反転の同型を両側に明示する。
使われ方：区間族の逆写像則。 -/
lemma intervalMappingReverseBack_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (g : A.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (intervalMappingReverseBack g) =
      (Δ[1] ◁ (SSet.opFunctorCompOpFunctorIso.app A).inv) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g) ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints _ _ _

/-- 概要：区間族を反転して戻すと元の族になる。
方針：展開して二重反転の公式と同型の往復則を使う。
規約：端点条件の証明の選択に依存しない。
使われ方：区間写像空間の反転の左逆則。 -/
lemma intervalMappingReverseBack_family {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    intervalMappingReverseBack (intervalMappingReverseFamily f) = f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective x y
  rw [intervalMappingReverseBack_uncurry, intervalMappingReverseFamily_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_double, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- 概要：反転した区間族を元の向きへ戻す操作は単射。
方針：展開の前後の同型を消去し、prism の反転の単射性を使う。
規約：任意のパラメーターと値域で成立する。
使われ方：反転の右逆則。 -/
lemma intervalMappingReverseBack_injective {A X : SSet.{u}} (x y : X _⦋0⦌) :
    Function.Injective (intervalMappingReverseBack (A := A) (x := x) (y := y)) := by
  intro f g h
  have he := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry h
  rw [intervalMappingReverseBack_uncurry, intervalMappingReverseBack_uncurry] at he
  have he' := (cancel_epi (Δ[1] ◁ (SSet.opFunctorCompOpFunctorIso.app A).inv)).1 he
  have he'' := (cancel_mono (SSet.opFunctorCompOpFunctorIso.app X).hom).1 he'
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _ (reversePrism_injective he'')

/-- 概要：区間族の反転は全パラメーターの族の型の同値。
方針：二重反転による左逆と、戻す操作の単射性から右逆を得る。
規約：モデル構造や Kan 性を用いない。
使われ方：区間写像空間の反転同型の全単体での全単射性。 -/
def intervalMappingReverseFamilyEquiv (A : SSet.{u}) {X : SSet.{u}} (x y : X _⦋0⦌) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) ≃
      (A.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)) where
  toFun := intervalMappingReverseFamily
  invFun := intervalMappingReverseBack
  left_inv := intervalMappingReverseBack_family
  right_inv g := intervalMappingReverseBack_injective x y
    (intervalMappingReverseBack_family (intervalMappingReverseBack g))

/-- 概要：端点固定の区間写像空間の反転から反転した二端点の区間写像空間への射。
方針：普遍的な区間族を反転する。
規約：x から y への区間を反対の単体集合の y から x への区間に写す。
使われ方：coherent 合成の反転した底のパラメーター比較。 -/
def intervalMappingReverse {X : SSet.{u}} (x y : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) :=
  intervalMappingReverseFamily (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y))

/-- 概要：区間族の反転は射そのものの反転と区間写像空間の反転射の合成。
方針：展開して prism の反転とパラメーター制限の自然性を使う。
規約：全パラメーターについての射の等式。
使われ方：反転した Hom の比較を同値の合成として同定する。 -/
lemma intervalMappingReverseFamily_eq {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    intervalMappingReverseFamily f = SSet.opFunctor.map f ≫ intervalMappingReverse x y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [intervalMappingReverseFamily_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    intervalMappingReverse, intervalMappingReverseFamily_uncurry,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_precomp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
