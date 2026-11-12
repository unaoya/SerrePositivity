module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderChain

/-!
概要：先頭が c の射列を Under c の射列として復元する。
方針：先頭から各頂点への射と元の合成則を使う。
規約：同じ宇宙の小さい圏を扱い、始対象性は仮定しない。
使われ方：B5 の pointwise Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {C : Type u} [Category.{u} C] (c : C)

/-- 概要：先頭が c に等しい射列から Under c の射列を作る。
方針：先頭の等式で始域を輸送し後続対象への射を使う。
規約：先頭の等式は証明データとして受け取る。
使われ方：coslice の逆方向の構成。 -/
def nerveUnderChainInverse {n : ℕ} (G : ComposableArrows C (n + 1)) (h : G.obj 0 = c) :
    ComposableArrows (Under c) n where
  obj i := Under.mk (eqToHom h.symm ≫ G.map (homOfLE (show (0 : Fin (n + 2)) ≤ i.succ by simp)))
  map {i j} f := Under.homMk (G.map ((Fin.succFunctor (n + 1)).map f)) (by
    change (eqToHom h.symm ≫ G.map _) ≫ G.map _ = eqToHom h.symm ≫ G.map _
    rw [Category.assoc, ← G.map_comp]
    rfl)
  map_id i := by
    apply Under.UnderMorphism.ext
    exact G.map_id i.succ
  map_comp f g := by
    apply Under.UnderMorphism.ext
    exact G.map_comp _ _

/-- 概要：前置した射列から元の Under の射列を回収する。
方針：各構造射の公式と通常の関手の拡張性を使う。
規約：全ての対象と射を回収する。
使われ方：単体ごとの左逆性。 -/
lemma nerveUnderChainInverse_chain {n : ℕ} (F : ComposableArrows (Under c) n) :
    nerveUnderChainInverse c (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderChain c F) rfl = F := by
  let hobj : ∀ i, (nerveUnderChainInverse c (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderChain c F) rfl).obj i = F.obj i := by
    intro i
    change Under.mk (eqToHom (Eq.refl c) ≫ _) = F.obj i
    rw [eqToHom_refl, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderChain_map_zero_succ]
    rfl
  refine CategoryTheory.Functor.ext hobj (fun i j f ↦ ?_)
  apply Under.UnderMorphism.ext
  simp only [Under.comp_right, Under.eqToHom_right]
  change (F.map f).right = eqToHom _ ≫ (F.map f).right ≫ eqToHom _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：Under の射列を復元してから前置すると元の射列になる。
方針：先頭・尾部・最初の射で比較する。
規約：先頭の等式による輸送を明記する。
使われ方：単体ごとの右逆性。 -/
lemma nerveUnderChain_chainInverse {n : ℕ} (G : ComposableArrows C (n + 1)) (h : G.obj 0 = c) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderChain c (nerveUnderChainInverse c G h) = G := by
  refine ComposableArrows.ext_succ h.symm rfl ?_
  simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderChain, nerveUnderChainInverse, ComposableArrows.precomp_map,
    eqToHom_refl, Category.comp_id]
  simp

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
