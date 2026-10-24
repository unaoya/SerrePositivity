module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.OverIso
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.HomotopyRecovery
public import SerrePositivity.InfinityCategories.Core.TerminalMappingSpace
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
/-!
概要：通常の終対象と nerve の終頂点を双方向に比較する。
方針：Over の忘却同型から自明 Kan 性を得て、逆向きはホモトピー圏で反映する。
規約：終対象構造の存在は Nonempty で表す。
使われ方：B5 の通常の極限錐と native な極限錐の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits SSet
open scoped Simplicial
universe u
noncomputable section
namespace SerrePositivity.InfinityCategories.F1B
variable {C : Type u} [Category.{u} C] {t : C}

/-- 概要：終対象への Over の忘却関手は圏の同型を与える。
方針：Over の射影とホモトピー圏への充満忠実な包含を使う。
規約：同じ宇宙の小さい圏の指定対象を保持する。
使われ方：B5 の局所極限の双方向比較。 -/
def overForgetIsoOfTerminal (ht : IsTerminal t) : Cat.of (Over t) ≅ Cat.of C where
  hom := (Over.forget t).toCatHom
  inv := (show C ⥤ Over t from
    { obj := fun x ↦ Over.mk (ht.from x)
      map := fun f ↦ Over.homMk f (ht.hom_ext _ _)
      map_id := fun _ ↦ Over.OverMorphism.ext rfl
      map_comp := fun _ _ ↦ Over.OverMorphism.ext rfl }).toCatHom
  hom_inv_id := by
    apply Cat.Hom.ext
    let ho : ∀ x : Over t, Over.mk (ht.from x.left) = x := by
      intro x
      have he : ht.from x.left = x.hom := ht.hom_ext _ _
      rw [he]
      rfl
    refine CategoryTheory.Functor.ext ho (fun x y f ↦ ?_)
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor, Functor.comp_map, Functor.id_map]
    apply Over.OverMorphism.ext
    erw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left]
    change f.left = eqToHom _ ≫ f.left ≫ eqToHom _
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  inv_hom_id := by apply Cat.Hom.ext; rfl

/-- 概要：通常の終対象は nerve の終頂点を与える。
方針：Over の射影とホモトピー圏への充満忠実な包含を使う。
規約：同じ宇宙の小さい圏の指定対象を保持する。
使われ方：B5 の局所極限の双方向比較。 -/
lemma nerveVertex_isTerminal (ht : IsTerminal t) : IsTerminalVertex (nerveVertex t) := by
  have hi : IsIso (nerveMap (Over.forget t)) :=
    nerveFunctor.map_isIso (overForgetIsoOfTerminal ht).hom
  have he : sliceOverProjection (nervePoint t) =
      (SerrePositivity.InfinityCategories.F1B.nerveOverIso t).inv ≫ nerveMap (Over.forget t) := by
    rw [← SerrePositivity.InfinityCategories.F1B.nerveOverIso_projection, Iso.inv_hom_id_assoc]
  have hq : IsIso (sliceOverProjection (nervePoint t)) := by rw [he]; infer_instance
  apply (isTerminalVertex_iff_trivialKanFibration (nerveVertex t)).2
  exact @isIso_trivialKanFibration _ _ (sliceOverProjection (nervePoint t)) hq

/-- 概要：nerve の終頂点から通常の終対象構造を復元する。
方針：Over の射影とホモトピー圏への充満忠実な包含を使う。
規約：同じ宇宙の小さい圏の指定対象を保持する。
使われ方：B5 の局所極限の双方向比較。 -/
def isTerminalOfNerveVertex (h : IsTerminalVertex (nerveVertex t)) : IsTerminal t := by
  let ht := h.isTerminalHo
  let ff := SerrePositivity.InfinityCategories.F1B.nerveHomotopyInclusion_fullyFaithful C
  refine IsTerminal.ofUniqueHom
    (fun x ↦ ff.preimage (ht.from ((SerrePositivity.InfinityCategories.F1B.nerveHomotopyInclusion C).obj x))) ?_
  intro x f
  apply ff.map_injective
  exact ht.hom_ext _ _

/-- 概要：通常の終対象構造の存在と nerve の終頂点性は同値。
方針：Over の射影とホモトピー圏への充満忠実な包含を使う。
規約：同じ宇宙の小さい圏の指定対象を保持する。
使われ方：B5 の局所極限の双方向比較。 -/
lemma nerveVertex_isTerminal_iff : Nonempty (IsTerminal t) ↔ IsTerminalVertex (nerveVertex t) :=
  ⟨fun ⟨h⟩ ↦ nerveVertex_isTerminal h, fun h ↦ ⟨isTerminalOfNerveVertex h⟩⟩
end SerrePositivity.InfinityCategories.F1B
