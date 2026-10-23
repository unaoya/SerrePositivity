module

public import SerrePositivity.InfinityCategories.F1.Simplicial.ReplacementInnerHorn
public import SerrePositivity.InfinityCategories.F1B.KanFinalHornFamily

/-!
概要：有限鎖上の replacement の最後の外ホーン上の図式を可逆化条件から延長する。
方針：始対象の係数との積を外ホーンの族として充填し、replacement の pushout で貼る。
規約：可逆性を課すのは指定した終端辺の族である。
使われ方：相対指数の特殊な辺の cartesian 性の模型側の充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：最後の外ホーン上の図式を始対象係数のパラメータ付き図式へ戻す。
方針：標準単体と有限鎖の nerve の同型と、部分底の組み立て射を使う。
規約：図式 F の係数値の充填性は不要。
使われ方：延長に必要な終端辺の可逆性を具体的に記述する。 -/
def kanReplacementFinalHornDiagram (n : ℕ)
    (F : ULift.{u} (Fin (n + 3)) ⥤ SSet.{u}) {D : SSet.{u}}
    (H : ((replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage
      (simplicialReplacementProjection F) : SSet.{u}) ⟶ D) :
    (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⊗ F.obj (ULift.up 0) ⟶ D :=
  ((subcomplexPreimageIso (horn (n + 2) (Fin.last (n + 2)))
    (stdSimplex.isoNerve (n + 2)).symm).inv ▷ F.obj (ULift.up 0)) ≫
    replacementInitialSubcomplexMap F (scaffoldFiniteInitial (n + 2))
      (replacementNerveHorn (n + 2) (Fin.last (n + 2))) ≫ H

/-- 概要：replacement の最後の外ホーン上の図式は指定終端辺の族が可逆なら延長できる。
方針：外ホーンと始対象係数の積の充填を、部分底と全体の pushout に沿って貼る。
規約：D は quasicategory、F は任意の単体集合値図式。
使われ方：cartesian ホーンの持ち上げを構成するための模型側の延長。 -/
lemma exists_kanReplacementFinalHorn_extension (n : ℕ)
    (F : ULift.{u} (Fin (n + 3)) ⥤ SSet.{u}) {D : SSet.{u}} [Quasicategory D]
    (H : ((replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage
      (simplicialReplacementProjection F) : SSet.{u}) ⟶ D)
    (he : ∀ x : (F.obj (ULift.up 0)) _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      ((kanReplacementFinalHornDiagram n F H).app (Opposite.op ⦋1⦌)
        (finalHornEdge n, PinchedHom.constant x 1)))) :
    ∃ G : simplicialReplacement F ⟶ D,
      ((replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage
        (simplicialReplacementProjection F)).ι ≫ G = H := by
  let A := replacementNerveHorn.{u} (n + 2) (Fin.last (n + 2))
  let K := F.obj (ULift.up 0)
  let e := subcomplexPreimageIso (horn (n + 2) (Fin.last (n + 2)))
    (stdSimplex.isoNerve.{u} (n + 2)).symm
  let k := replacementInitialSubcomplexMap F (scaffoldFiniteInitial (n + 2)) A
  obtain ⟨L, hL⟩ := exists_kanFinalHornFamily_extension n (kanReplacementFinalHornDiagram n F H) he
  let L' := ((stdSimplex.isoNerve.{u} (n + 2)).inv ▷ K) ≫ L
  have hι : e.hom ≫ (horn (n + 2) (Fin.last (n + 2))).ι =
      A.ι ≫ (stdSimplex.isoNerve (n + 2)).inv := rfl
  have hL' : (A.ι ▷ K) ≫ L' = k ≫ H := by
    dsimp only [L']
    rw [← Category.assoc, ← comp_whiskerRight, ← hι, comp_whiskerRight, Category.assoc, hL]
    change (e.hom ▷ K) ≫ (e.inv ▷ K) ≫ k ≫ H = _
    rw [← Category.assoc, ← comp_whiskerRight, e.hom_inv_id, id_whiskerRight, Category.id_comp]
  let q := replacementInitialSubcomplex_isPushout F (scaffoldFiniteInitial (n + 2)) A
    (replacementNerveHorn_contains_noninitial (n + 2) (Fin.last (n + 2)) (by
      change (0 : ℕ) < n + 2
      omega))
  exact ⟨q.desc H L' hL'.symm, q.inl_desc _ _ _⟩

end SerrePositivity.InfinityCategories
