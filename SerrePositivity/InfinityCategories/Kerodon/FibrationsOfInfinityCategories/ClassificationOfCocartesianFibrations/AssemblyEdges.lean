module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementAssembly

/-!
概要：定値係数からの組み立て射の水平辺を計算する。
方針：定値単体の Yoneda 表示と係数変換を計算する。
規約：底の圏と係数の単体集合は任意。
使われ方：外ホーンの終端辺の族を scaffold の cocartesian 辺と同定する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：組み立て射は底の辺と定値係数を水平辺へ送る。
方針：定値単体の射への復元と定値射への後合成を計算する。
規約：係数自然変換の始点での成分を使う。
使われ方：模型の終端辺の可逆化条件を実際の cocartesian 辺から導く。 -/
lemma simplicialReplacementAssembly_horizontal
    {C : Type u} [Category.{u} C] {K : SSet.{u}} {F : C ⥤ SSet.{u}}
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F)
    {c d : C} (f : c ⟶ d) (x : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementAssembly η).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ f, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianScaffoldHorizontalEdge F f ((η.app c).app (Opposite.op ⦋0⦌) x) := by
  change (⟨ComposableArrows.mk₁ f,
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) ≫ η.app c⟩ :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F) _⦋1⦌) = _
  have hc : SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) =
      (SSet.const x : (Δ[1] : SSet.{u}) ⟶ K) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [hc, SSet.const_comp]
  rfl

/-- 概要：scaffold に後合成した組み立て射の定値係数の辺は cocartesian。
方針：水平辺の計算を scaffold の水平辺条件に渡す。
規約：scaffold の fiber 条件はこの結論には使わない。
使われ方：最後の外ホーンの族の可逆化条件への入力。 -/
lemma CocartesianScaffold.assembly_horizontal_isCocartesian
    {C : Type u} [Category.{u} C] {E K : SSet.{u}} {p : E ⟶ nerve C}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] {F : C ⥤ SSet.{u}} [∀ c, Quasicategory (F.obj c)]
    {l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E}
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianScaffold p F l)
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F)
    {c d : C} (f : c ⟶ d) (x : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementAssembly η ≫ l).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ f, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (l.app (Opposite.op ⦋1⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementAssembly η).app (Opposite.op ⦋1⦌) _))
  rw [simplicialReplacementAssembly_horizontal]
  exact hs.horizontal f _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianScaffold export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianScaffold (assembly_horizontal_isCocartesian)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
