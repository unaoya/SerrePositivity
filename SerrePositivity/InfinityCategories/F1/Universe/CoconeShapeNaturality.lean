module

public import SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexShapes
/-!
概要：標準単体付き余錐形状の宇宙同型は、元のパラメーターの全射で自然。
方針：join の宇宙比較の自然性を、右因子の標準単体同型と合成する。
規約：全次数と元の全射を厳密に保持する。
使われ方：Ind の補間余錐の終点面の宇宙比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
/-- 概要：余錐形状の順方向の宇宙比較は、元のパラメーターの射と可換。
方針：join の自然性を使う。規約：厳密な等式。使われ方：指定変換下の余錐の比較。 -/
lemma uliftCoconeShapeIso_hom_naturality {A B : SSet.{u}} (f : A ⟶ B) (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).map (joinMap f (𝟙 (Δ[n] : SSet.{u}))) ≫
      (uliftCoconeShapeIso.{u, v} B n).hom =
    (uliftCoconeShapeIso.{u, v} A n).hom ≫
      joinMap ((SSet.uliftFunctor.{v, u}).map f) (𝟙 (Δ[n] : SSet.{max u v})) := by
  simp only [uliftCoconeShapeIso, Iso.trans_hom, joinIso, Category.assoc]
  rw [← Category.assoc, uliftJoinIso_hom_naturality]
  simp only [Category.assoc, ← joinMap_comp, Iso.refl_hom, Category.comp_id, Category.id_comp]
  rfl
end SerrePositivity.InfinityCategories
