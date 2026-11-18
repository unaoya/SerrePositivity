module

public import SerrePositivity.InfinityCategories.Sheaves.RelativeCechDiagonal
public import SerrePositivity.InfinityCategories.Sheaves.PresheafRelativeCechHom

/-!
概要：同じ相対 Čech 冪の各点の元を、元の全座標で比較する。
方針：既存 Yoneda 対応で各点の元を射へ移し、忘却後の同じ座標の外延性を使う。
規約：HTT 6.2.2.6 の Čech 解消への表示の法則。点での有限極限を選び直さない。
使われ方：S8 の対角の像篩と、全座標の等化篩との照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}

/-- 同じ Čech 冪の元は、元の射影を評価した全座標で決まる。 -/
lemma presheafRelativeCech_proj_app_ext (f : P ⟶ Q) (n : ℕ) (U : C)
    {x y : (((relativeCechData f).obj.obj (Opposite.op ⦋n⦌)).left).obj (Opposite.op U)}
    (he : ∀ i : Fin (n + 1), ((relativeCechData f).proj n i).left.app (Opposite.op U) x =
      ((relativeCechData f).proj n i).left.app (Opposite.op U) y) : x = y := by
  apply (yonedaEquiv (X := U)
    (F := ((relativeCechData f).obj.obj (Opposite.op ⦋n⦌)).left)).symm.injective
  apply relativeCech_proj_hom_ext f n
  intro i
  rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, he i]

end SerrePositivity.InfinityCategories.Sheaves
