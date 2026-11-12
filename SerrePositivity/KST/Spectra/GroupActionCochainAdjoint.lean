module

public import SerrePositivity.KST.Spectra.GroupActionAdjoint
public import SerrePositivity.KST.Spectra.PointedActionCochainCotensor
public import SerrePositivity.KST.Spectra.GroupActionCochainKan

/-!
概要：作用スペクトルの余単体 cochain の随伴構造射と全基点 π_* 同型。
方針：元の同変な随伴射を cochain に送り、loop 交換同型の逆を合成する。
規約：随伴射は余単体の自然変換として厳密に構成する。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain の Kan Ω 列の構造。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：cochain の一段から次段の loop への実際の余単体自然変換。
方針：係数の同変な随伴構造射の cochain と loop 交換の逆を合成する。
規約：元の構造射を厳密 Ω 同型へ置き換えない。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。各 cochain 次数のスペクトル構造。 -/
def adjointTransformation {G : Type u} [Group G] (A : GroupAction.{u} G) (n : ℕ) :
    level A n ⟶ level A (n + 1) ⋙ ihom PointedSimplicialSet.circle.{u} :=
  let B := (GroupAction.levelFunctor G n).obj A
  let C := (GroupAction.levelFunctor G (n + 1)).obj A
  let L := ((ihom PointedSimplicialSet.circle.{u}).mapAction G).obj C
  let θ : PointedActionCochains.obj B ⟶ PointedActionCochains.obj L :=
    PointedActionCochains.map (G := G) (B := B) (C := L) (GroupAction.adjointMap A n)
  let e : PointedActionCochains.obj C ⋙ ihom PointedSimplicialSet.circle.{u} ≅
      PointedActionCochains.obj L :=
    PointedActionCochains.cotensorIso PointedSimplicialSet.circle.{u} C
  θ ≫ e.inv

/-- 概要：cochain の随伴構造射は全ての余単体次数で全基点 π_* 同型。
方針：元の Ω 条件、cochain の係数の同型保存、loop 交換同型を合成する。
規約：群の有限性や有理性は不要。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain の Ω 条件。 -/
lemma adjointTransformation_piIsomorphism {G : Type u} [Group G]
    (A : GroupAction.{u} G) (n : ℕ) (j : SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (X := ((level A n).obj j).right)
      (Y := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((level A (n + 1)).obj j)).right)
      ((adjointTransformation A n).app j).right := by
  let B := (GroupAction.levelFunctor G n).obj A
  let C := (GroupAction.levelFunctor G (n + 1)).obj A
  let L := ((ihom PointedSimplicialSet.circle.{u}).mapAction G).obj C
  let : KanComplex B.V.right := inferInstanceAs (KanComplex (A.V.level n).space.right)
  let : KanComplex C.V.right := inferInstanceAs (KanComplex (A.V.level (n + 1)).space.right)
  let : KanComplex L.V.right :=
    inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (A.V.level (n + 1)).space).right)
  have h := PointedActionCochains.map_piIsomorphism (GroupAction.adjointMap A n)
    (GroupAction.adjointMap_piIsomorphism A n) j
  let e : ((PointedActionCochains.obj L).obj j).right ≅
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((level A (n + 1)).obj j)).right :=
    PointedSimplicialSet.forget.mapIso
      ((PointedActionCochains.cotensorIso PointedSimplicialSet.circle.{u} C).app j).symm
  exact h.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e)

end

end SerrePositivity.KST.Spectra.GroupActionCochains
