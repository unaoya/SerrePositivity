module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowReindex

/-!
概要：係数の自然変換を、同じ基底射列のbarの全行の射へ送る。
方針：各余積成分へ元の同じ係数射を適用し、面・退化とは元の自然性で合わせる。
規約：元の基底射列を全次数で保持する。
使われ方：IS-W2 R03f.2の元のsimplicialReplacementMapとの照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
variable {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}} (η : F ⟶ G)

/-- 元の同じ係数射を、各基底射列の余積成分へ適用する。 -/
def simplicialReplacementRowMap (n : ℕ) :
    simplicialReplacementRow F n ⟶ simplicialReplacementRow G n where
  app q := ↾fun s => ⟨s.1, (η.app (s.1.obj 0)).app q s.2⟩
  naturality q q' θ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ,x⟩
    exact congrArg (Sigma.mk σ)
      (ConcreteCategory.congr_hom ((η.app (σ.obj 0)).naturality θ) x)

/-- 同じ行の射は、全ての面・退化と元の係数の自然性で可換する。 -/
theorem simplicialReplacementRowMap_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    simplicialReplacementRowReindex F α ≫ simplicialReplacementRowMap η m.len =
      simplicialReplacementRowMap η n.len ≫ simplicialReplacementRowReindex G α := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  rintro ⟨σ,x⟩
  refine Sigma.ext (show α.toOrderHom.monotone.functor ⋙ σ =
    α.toOrderHom.monotone.functor ⋙ σ from rfl) ?_
  apply heq_of_eq
  exact ConcreteCategory.congr_hom
    (congr_app (η.naturality (σ.map (homOfLE (Fin.zero_le (α.toOrderHom 0))))) q) x

/-- 元の係数射を、barの全行の一つの自然変換に束ねる。 -/
def simplicialReplacementRowsMap : simplicialReplacementRows F ⟶ simplicialReplacementRows G where
  app n := simplicialReplacementRowMap η n.unop.len
  naturality n m α := simplicialReplacementRowMap_reindex η α.unop

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
