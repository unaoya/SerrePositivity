module

public import SerrePositivity.InfinityCategories.F1B.KanCocartesianScaffold
public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacementAssembly

/-!
概要：定値係数からの組み立て射の水平辺を計算する。
方針：定値単体の Yoneda 表示と係数変換を計算する。
規約：底の圏と係数の単体集合は任意。
使われ方：外ホーンの終端辺の族を scaffold の cocartesian 辺と同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：組み立て射は底の辺と定値係数を水平辺へ送る。
方針：定値単体の射への復元と定値射への後合成を計算する。
規約：係数自然変換の始点での成分を使う。
使われ方：模型の終端辺の可逆化条件を実際の cocartesian 辺から導く。 -/
lemma kanSimplicialReplacementAssembly_horizontal
    {C : Type u} [Category.{u} C] {K : SSet.{u}} {F : C ⥤ SSet.{u}}
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F)
    {c d : C} (f : c ⟶ d) (x : K _⦋0⦌) :
    (simplicialReplacementAssembly η).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ f, PinchedHom.constant x 1) =
      kanScaffoldHorizontalEdge F f ((η.app c).app (Opposite.op ⦋0⦌) x) := by
  change (⟨ComposableArrows.mk₁ f,
    SSet.yonedaEquiv.symm (PinchedHom.constant x 1) ≫ η.app c⟩ :
      (simplicialReplacement F) _⦋1⦌) = _
  have hc : SSet.yonedaEquiv.symm (PinchedHom.constant x 1) =
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
lemma KanCocartesianScaffold.assembly_horizontal_isCocartesian
    {C : Type u} [Category.{u} C] {E K : SSet.{u}} {p : E ⟶ nerve C}
    [CocartesianFibration p] {F : C ⥤ SSet.{u}} [∀ c, Quasicategory (F.obj c)]
    {l : simplicialReplacement F ⟶ E}
    (hs : KanCocartesianScaffold p F l)
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F)
    {c d : C} (f : c ⟶ d) (x : K _⦋0⦌) :
    IsCocartesianEdge p ((simplicialReplacementAssembly η ≫ l).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ f, PinchedHom.constant x 1)) := by
  change IsCocartesianEdge p (l.app (Opposite.op ⦋1⦌)
    ((simplicialReplacementAssembly η).app (Opposite.op ⦋1⦌) _))
  rw [kanSimplicialReplacementAssembly_horizontal]
  exact hs.horizontal f _

end SerrePositivity.InfinityCategories
