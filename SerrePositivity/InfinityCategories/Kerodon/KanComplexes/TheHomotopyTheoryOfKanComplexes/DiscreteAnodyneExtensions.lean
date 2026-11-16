module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.PiZeroConstant
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneRelativeHomotopy

/-!
概要：離散値の図式で、成分ごとの anodyne 射に沿う延長を一意に貼り合わせる。
方針：既存の相対ホモトピーと離散値の二射の等式を組み合わせ、Kan 性で延長する。
規約：添字の圏は任意の小さい通常の圏。単体集合の図式に fibrancy を仮定しない。
Kerodon §3.1（Tag 00SZ）の既存の離散模型・ホモトピーの法則。
使われ方：離散空間値の図式の任意小極限の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet HomotopicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- anodyne 射への制限は、同じ離散単体集合への射を単射に送る。
相対ホモトピーの存在と既存の離散値の等式の法則を使う。 -/
lemma discrete_precomp_injective_of_anodyne {A B : SSet.{u}}
    (i : A ⟶ B) (hi : anodyneExtensions i) (T : Type u) :
    Function.Injective (fun f : B ⟶ (Functor.const SimplexCategoryᵒᵖ).obj T => i ≫ f) := by
  letI := discrete_kan T
  intro f g h
  obtain ⟨H, _⟩ := anodyne_relative_homotopy i hi f g h
  exact SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.homotopy_eq H

/-- 離散単体集合への射は、anodyne 射に沿って一意に延長できる。 -/
lemma existsUnique_discrete_extension {A B : SSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i) (T : Type u)
    (a : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj T) :
    ∃! b : B ⟶ (Functor.const SimplexCategoryᵒᵖ).obj T, i ≫ b = a := by
  letI := discrete_kan T
  have := hi (terminal.from ((Functor.const SimplexCategoryᵒᵖ).obj T))
    (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  have sq : CommSq a i (terminal.from ((Functor.const SimplexCategoryᵒᵖ).obj T))
      (terminal.from B) := ⟨terminal.hom_ext _ _⟩
  refine ⟨sq.lift, sq.fac_left, ?_⟩
  intro b hb
  exact discrete_precomp_injective_of_anodyne i hi T (hb.trans sq.fac_left.symm)

/-- 成分ごとの一意な離散延長は、元の図式の自然変換として貼り合う。
自然性を追加の仮定にせず、同じ anodyne 射への制限の単射性から証明する。 -/
lemma discreteDiagram_anodyne_extensions {I : Type u} [SmallCategory I] (F : I ⥤ Type u)
    {A B : I ⥤ SSet.{u}} (ι : A ⟶ B) (hι : ∀ i, anodyneExtensions (ι.app i))
    (a : A ⟶ F ⋙ Functor.const SimplexCategoryᵒᵖ) :
    ∃ b : B ⟶ F ⋙ Functor.const SimplexCategoryᵒᵖ, ι ≫ b = a := by
  choose b hb using fun i =>
    (existsUnique_discrete_extension (ι.app i) (hι i) (F.obj i) (a.app i)).exists
  refine ⟨{ app := b, naturality := ?_ }, ?_⟩
  · intro i k f
    apply discrete_precomp_injective_of_anodyne (ι.app i) (hι i) (F.obj k)
    calc
      ι.app i ≫ (B.map f ≫ b k) = A.map f ≫ (ι.app k ≫ b k) := by
        rw [← Category.assoc, ← ι.naturality, Category.assoc]
      _ = A.map f ≫ a.app k := by rw [hb k]
      _ = a.app i ≫ (F ⋙ Functor.const SimplexCategoryᵒᵖ).map f := a.naturality f
      _ = ι.app i ≫ (b i ≫ (F ⋙ Functor.const SimplexCategoryᵒᵖ).map f) := by
        rw [← Category.assoc, hb i]
  · apply NatTrans.ext
    funext i
    exact hb i

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
