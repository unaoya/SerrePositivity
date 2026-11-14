module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRows

/-!
概要：元の基底射列の行の面・退化作用を、同じ始点の係数の輸送で与える。
方針：任意の単調写像で基底射列を制限し、元の始点から新たな始点への射を適用する。
規約：係数の単体次数と基底射列の次数を独立に保つ。
使われ方：IS-W2 R03f.2の二重単体集合とその相対latchingの計算。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

/-- 同じ行の面・退化は、元の始点の係数を新たな始点へ運ぶ。 -/
def simplicialReplacementRowReindex {m n : SimplexCategory} (α : m ⟶ n) :
    simplicialReplacementRow F n.len ⟶ simplicialReplacementRow F m.len where
  app q := ↾fun s => ⟨α.toOrderHom.monotone.functor ⋙ s.1,
    (F.map (s.1.map (homOfLE (Fin.zero_le (α.toOrderHom 0))))).app q s.2⟩
  naturality q q' θ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ,x⟩
    exact congrArg (Sigma.mk (α.toOrderHom.monotone.functor ⋙ σ))
      (ConcreteCategory.congr_hom ((F.map (σ.map
        (homOfLE (Fin.zero_le (α.toOrderHom 0))))).naturality θ) x)

/-- 元の始点で恒等作用素は係数も変えない。 -/
theorem simplicialReplacementRowReindex_id (n : SimplexCategory) :
    simplicialReplacementRowReindex F (𝟙 n) = 𝟙 (simplicialReplacementRow F n.len) := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  rintro ⟨σ,x⟩
  refine Sigma.ext (show (𝟙 n : n ⟶ n).toOrderHom.monotone.functor ⋙ σ = σ from rfl) ?_
  apply heq_of_eq
  change (F.map (σ.map (𝟙 (0 : Fin (n.len+1))))).app q x = x
  rw [σ.map_id, F.map_id]
  rfl

/-- 行の全作用素の合成は、元の基底射列と係数の合成則である。 -/
theorem simplicialReplacementRowReindex_comp {l m n : SimplexCategory}
    (α : l ⟶ m) (β : m ⟶ n) :
    simplicialReplacementRowReindex F (α ≫ β) =
      simplicialReplacementRowReindex F β ≫ simplicialReplacementRowReindex F α := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  rintro ⟨σ,x⟩
  refine Sigma.ext (show (α ≫ β).toOrderHom.monotone.functor ⋙ σ =
    α.toOrderHom.monotone.functor ⋙ β.toOrderHom.monotone.functor ⋙ σ from rfl) ?_
  apply heq_of_eq
  change (F.map (σ.map (homOfLE (Fin.zero_le ((α ≫ β).toOrderHom 0))))).app q x =
    ((F.map (σ.map (homOfLE (Fin.zero_le (β.toOrderHom 0)))) ≫
      F.map (σ.map (β.toOrderHom.monotone.functor.map
        (homOfLE (Fin.zero_le (α.toOrderHom 0)))))).app q) x
  rw [← F.map_comp, ← σ.map_comp]
  rfl

/-- 元の基底射列を動かす行を、一つの単体的単体集合の図式にする。 -/
def simplicialReplacementRows : SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj n := simplicialReplacementRow F n.unop.len
  map α := simplicialReplacementRowReindex F α.unop
  map_id n := simplicialReplacementRowReindex_id F n.unop
  map_comp α β := simplicialReplacementRowReindex_comp F β.unop α.unop

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
