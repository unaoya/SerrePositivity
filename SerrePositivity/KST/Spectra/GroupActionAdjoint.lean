module

public import SerrePositivity.KST.Spectra.GroupAction
public import SerrePositivity.KST.Spectra.OmegaTransitionNaturality

/-!
概要：作用スペクトルの随伴構造射の点つき同変射としての構成。
方針：スペクトルの厳密な作用射が随伴構造射と可換なことを使う。
規約：厳密な Ω 同型は要求せず、全基点 π_* 同型を保持する。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。群作用の cochain の Ω 構造の係数。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.GroupAction

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：作用スペクトルの随伴構造射は各段の作用を保つ実際の射。
方針：群の各元の作用のスペクトル射の随伴可換式を使う。
規約：終域は次段の点つき loop の作用。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain の随伴構造射の係数。 -/
def adjointMap {G : Type u} [Group G] (A : GroupAction.{u} G) (n : ℕ) :
    (levelFunctor G n).obj A ⟶
      ((ihom PointedSimplicialSet.circle.{u}).mapAction G).obj ((levelFunctor G (n + 1)).obj A) where
  hom := OmegaSpectrum.adjointStructure A.V n
  comm g := OmegaSpectrum.adjointStructure_comm (A.ρ g).asHom n

/-- 概要：同変な随伴構造射の基礎射は全基点 π_* 同型。
方針：元の BF 対象の Ω 条件をそのまま取り出す。
規約：零次数の成分集合も含む。
使われ方：HA §1.4.2、BF 1978 §2。cochain の Ω 条件の入力。 -/
lemma adjointMap_piIsomorphism {G : Type u} [Group G] (A : GroupAction.{u} G) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (X := (A.V.level n).space.right)
      (Y := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (A.V.level (n + 1)).space).right) (adjointMap A n).hom.right :=
  A.V.omega_condition n

/-- 概要：同変な随伴構造射は作用スペクトルの射に自然。
方針：元の BF 射の随伴構造可換式を作用の射の外延性へ渡す。
規約：点つき作用の圏の厳密な等式。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain の Ω 列の射の構成。 -/
lemma adjointMap_natural {G : Type u} [Group G] {A B : GroupAction.{u} G}
    (f : A ⟶ B) (n : ℕ) :
    (levelFunctor G n).map f ≫ adjointMap B n = adjointMap A n ≫
      ((ihom PointedSimplicialSet.circle.{u}).mapAction G).map ((levelFunctor G (n + 1)).map f) := by
  apply Action.hom_ext
  exact OmegaSpectrum.adjointStructure_comm f.hom n

end

end SerrePositivity.KST.Spectra.GroupAction
