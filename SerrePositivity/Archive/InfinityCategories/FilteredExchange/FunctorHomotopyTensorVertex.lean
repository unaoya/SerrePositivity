module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyTensorRight
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：全係数を加えた元の円柱の頂点制限は同じ実頂点辺と係数の作用。
方針：同じ時刻と独立係数の二成分を全次数で計算する。
規約：実円柱と全係数を保持する。
使われ方：零面の終点像を元の Hom の全係数作用として読む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全係数円柱の頂点制限は元の実頂点辺を同じ全係数で作用させた射。 -/
lemma functorHomotopyTensorRight_postcomp_vertex {X Z Y : SSet.{u}} {f g : X ⟶ Z}
    (H : SSet.Homotopy f g) (A : SSet.{u}) (E : Z ⊗ A ⟶ Y) (x : X _⦋0⦌) :
    (lift (SSet.const x) (𝟙 A) ▷ Δ[1]) ≫
      (functorHomotopyPostcomp (functorHomotopyTensorRight H A) E).h =
    lift (snd A Δ[1] ≫ (lift (SSet.const x) (𝟙 Δ[1]) ≫ H.h)) (fst A Δ[1]) ≫ E := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨a, t⟩
  rfl

end SerrePositivity.InfinityCategories.F2
