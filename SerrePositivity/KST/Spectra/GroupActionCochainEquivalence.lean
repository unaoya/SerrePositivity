module

public import SerrePositivity.KST.Spectra.PointedActionCochainEquivalence
public import SerrePositivity.KST.Spectra.GroupActionCochainKan

/-!
概要：作用スペクトルの各段の π_* 同型は余単体 cochain の各次数でも同型。
方針：各段を点つき単体集合の作用へ評価し、自由軌道による cochain の不変性を使う。
規約：群の有限性や有理性は不要。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。スペクトルの cochain と hG の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：同変な BF 射の一段の全基点 π_* 同型は全ての cochain 次数でも全基点 π_* 同型。
方針：一段の点つき作用の cochain のホモトピー不変性へ帰着する。
規約：スペクトルの全段の条件ではなく指定段 k の条件だけを使う。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。作用スペクトルの余単体模型の係数比較。 -/
lemma levelMap_piIsomorphism {G : Type u} [Group G]
    {A B : GroupAction.{u} G} (f : A ⟶ B) (k : ℕ)
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.hom.app k).right) (j : SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (X := ((level A k).obj j).right) (Y := ((level B k).obj j).right)
      ((levelMap f k).app j).right := by
  let A₀ := (GroupAction.levelFunctor G k).obj A
  let B₀ := (GroupAction.levelFunctor G k).obj B
  let : KanComplex A₀.V.right := inferInstanceAs (KanComplex (A.V.level k).space.right)
  let : KanComplex B₀.V.right := inferInstanceAs (KanComplex (B.V.level k).space.right)
  exact PointedActionCochains.map_piIsomorphism ((GroupAction.levelFunctor G k).map f) hf j

end

end SerrePositivity.KST.Spectra.GroupActionCochains
