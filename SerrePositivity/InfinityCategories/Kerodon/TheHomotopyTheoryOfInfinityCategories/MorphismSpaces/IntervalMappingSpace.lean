module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：両端を固定した単位区間からの写像空間とパラメータ付きの普遍性。
方針：境界への制限の内部 Hom の頂点 fiber を取り、閉構造で族を展開する。
規約：標的の Kan 性を仮定せず、ここでは Kan 性や比較の同値性を主張しない。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、左右の pinched 写像空間を比較する中間模型。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：区間の境界を二つの指定頂点へ送る射。
方針：境界の単体の唯一の値が零なら x、一なら y の定値単体へ送る。
規約：境界上で異なる端点が同じ頂点を表していてもよい。
使われ方：Kerodon §4.6.5（Tag 01KW）、区間模型の固定端点の指定。 -/
def intervalMappingBoundary {X : SSet.{u}} (x y : X _⦋0⦌) :
    (boundary 1 : SSet.{u}) ⟶ X where
  app d := by
    obtain ⟨⟨d⟩⟩ := d
    exact ↾fun s ↦ if s.val 0 = 0 then
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x d else _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y d
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro s
    change (if s.val (α.unop.toOrderHom 0) = 0 then
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x m else _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y m) =
        X.map α (if s.val 0 = 0 then _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n else _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.boundaryOne_simplex_constant s]
    split <;> exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback _ α.unop).symm

/-- 概要：x と y を両端に持つ区間の写像の単体集合。
方針：区間から X への内部 Hom を、指定した境界の図式の上に制限する。
規約：各パラメータ次数でも境界の図式を厳密に固定する。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、左右の模型の共通比較先。 -/
@[kerodon 01J5, kerodon 03X9]
def intervalMappingSpace {X : SSet.{u}} (x y : X _⦋0⦌) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre (boundary 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (intervalMappingBoundary x y))

/-- 概要：区間の写像空間への族を区間とパラメータの直積からの射へ展開する。
方針：fiber の包含を内部 Hom に続けて uncurry する。
規約：区間を第一因子、パラメータを第二因子に置く。
使われ方：Kerodon §4.6.6（Tag 04HY）、写像空間の族の比較。 -/
def intervalMappingUncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) : (Δ[1] : SSet.{u}) ⊗ A ⟶ X :=
  uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (boundary 1).ι).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (intervalMappingBoundary x y)))

/-- 概要：展開した区間の族は境界上で指定した両端に定値。
方針：制限と uncurry の整合性、および fiber の条件を使う。
規約：境界のパラメータ成分は第一射影で忘れる。
使われ方：Kerodon §4.6.6（Tag 04HY）、区間模型の相対条件。 -/
lemma intervalMappingUncurry_boundary {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    ((boundary 1).ι ▷ A) ≫ intervalMappingUncurry f =
      fst (boundary 1 : SSet.{u}) A ≫ intervalMappingBoundary x y := by
  unfold intervalMappingUncurry
  rw [← uncurry_pre_app, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 概要：境界で両端を固定した区間の族を写像空間への族に戻す。
方針：curry した射の境界への制限を計算し、fiber へ持ち上げる。
規約：境界の条件は厳密な等式。
使われ方：Kerodon §4.6.6（Tag 04HY）、区間模型の普遍性の逆向き。 -/
def intervalMappingCurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h : ((boundary 1).ι ▷ A) ≫ H =
      fst (boundary 1 : SSet.{u}) A ≫ intervalMappingBoundary x y) :
    A ⟶ intervalMappingSpace x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (curry H) (by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
    exact h)

/-- 概要：区間の族を curry して展開すると元の族。
方針：fiber の包含の式と curry・uncurry の往復を使う。
規約：境界の条件の証明には依存しない。
使われ方：Kerodon §4.6.6（Tag 04HY）、区間模型の普遍性の往復。 -/
lemma intervalMappingUncurry_curry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h : ((boundary 1).ι ▷ A) ≫ H =
      fst (boundary 1 : SSet.{u}) A ≫ intervalMappingBoundary x y) :
    intervalMappingUncurry (intervalMappingCurry H h) = H := by
  unfold intervalMappingUncurry intervalMappingCurry
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, uncurry_curry]

/-- 概要：写像空間への族は展開した区間の族で一意に決まる。
方針：uncurry の単射性と fiber の包含の単射性を使う。
規約：任意のパラメータ A。
使われ方：Kerodon §4.6.6（Tag 04HY）、区間模型の比較射の一意性。 -/
lemma intervalMappingUncurry_injective {A X : SSet.{u}} (x y : X _⦋0⦌) :
    Function.Injective (intervalMappingUncurry (A := A) (x := x) (y := y)) := by
  intro f g h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((pre (boundary 1).ι).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (intervalMappingBoundary x y))
  exact uncurry_injective h

/-- 概要：写像空間への族を展開して curry すると元の族。
方針：uncurry の単射性で区間上の射の往復へ戻す。
規約：固定条件は展開した族の境界の式。
使われ方：Kerodon §4.6.6（Tag 04HY）、区間模型の普遍性の逆方向の往復。 -/
lemma intervalMappingCurry_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    intervalMappingCurry (intervalMappingUncurry f) (intervalMappingUncurry_boundary f) = f := by
  apply intervalMappingUncurry_injective x y
  exact intervalMappingUncurry_curry _ _

/-- 概要：区間の族への展開はパラメータの前合成と可換。
方針：内部 Hom の uncurry の自然性を使う。
規約：区間は第一因子のまま固定する。
使われ方：Kerodon §4.6.6（Tag 04HY）、パラメータの境界への制限。 -/
lemma intervalMappingUncurry_precomp {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (i : A ⟶ B) (f : B ⟶ intervalMappingSpace x y) :
    intervalMappingUncurry (i ≫ f) = (Δ[1] ◁ i) ≫ intervalMappingUncurry f := by
  unfold intervalMappingUncurry
  rw [Category.assoc, uncurry_natural_left]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
