module

public import SerrePositivity.KST.Spectra.SimplexDensityNaturality
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
概要：共通の添字圏上の図式に対するパラメーター付き標準単体の密度。
方針：各対象の整合する族を貼り合わせ、対角評価の三変数への自然性を使う。
規約：通常の図式の自然変換を扱い、Kan 条件や ∞ 極限を仮定しない。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。重み付き end と Tot の比較の普遍性。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.SimplexDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I] (W H : I ⥤ SSet.{u}) (A : SSet.{u})

/-- 概要：図式上の各対象の標準単体の族と添字の射への整合条件。
方針：重みの前合成と係数の後合成が一致することを要求する。
規約：パラメーターは全ての添字で共通。
使われ方：Goerss–Jardine VIII §1。二つの end の順序交換の具体的な族。 -/
structure DiagramFamily where
  app (i : I) : Family (W.obj i) A (H.obj i)
  naturality {i j : I} (f : i ⟶ j) :
    (app j).preWeight (W.map f) = (app i).postCoefficient (H.map f)

variable {W H A}

/-- 概要：図式上の整合する標準単体の族を対角評価する。
方針：各対象で対角評価し、重み・係数への自然性を使う。
規約：実際の自然変換を与える。
使われ方：Goerss–Jardine VIII §1。Tot から重みの end への射の普遍性。 -/
def diagramDiagonal (s : DiagramFamily W H A) : W ⊗ (Functor.const I).obj A ⟶ H where
  app i := diagonal (W.obj i) A (H.obj i) (s.app i)
  naturality i j f := by
    change (W.map f ▷ A) ≫ diagonal _ _ _ (s.app j) =
      diagonal _ _ _ (s.app i) ≫ H.map f
    rw [← diagonal_preWeight, ← diagonal_postCoefficient, s.naturality f]

/-- 概要：パラメーター付き図式の射を標準単体上の整合する族に展開する。
方針：各成分を展開し、対角評価の単射性で自然性を確認する。
規約：図式やパラメーターの Kan 性は不要。
使われ方：Goerss–Jardine VIII §1。密度による比較の逆の普遍性。 -/
def diagramExpand (t : W ⊗ (Functor.const I).obj A ⟶ H) : DiagramFamily W H A where
  app i := expand (t.app i)
  naturality {i j} f := by
    apply (familyEquiv (S := W.obj i) (A := A) (Y := H.obj j)).symm.injective
    change diagonal _ _ _ ((expand (t.app j)).preWeight (W.map f)) =
      diagonal _ _ _ ((expand (t.app i)).postCoefficient (H.map f))
    rw [diagonal_preWeight, diagonal_postCoefficient, diagonal_expand, diagonal_expand]
    exact t.naturality f

@[ext]
lemma DiagramFamily.ext {s t : DiagramFamily W H A} (h : ∀ i, s.app i = t.app i) : s = t := by
  cases s
  cases t
  congr
  funext i
  exact h i

lemma diagramDiagonal_expand (t : W ⊗ (Functor.const I).obj A ⟶ H) :
    diagramDiagonal (diagramExpand t) = t := by
  apply NatTrans.ext
  funext i
  exact diagonal_expand (t.app i)

lemma diagramExpand_diagonal (s : DiagramFamily W H A) :
    diagramExpand (diagramDiagonal s) = s := by
  apply DiagramFamily.ext
  intro i
  exact expand_diagonal (s.app i)

/-- 概要：パラメーター付き図式の射と標準単体上の図式の族の同値。
方針：展開と対角評価の両逆を束ねる。
規約：図式の通常の自然変換に対する集合の同値。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。end と Tot の模型比較。 -/
def diagramFamilyEquiv : (W ⊗ (Functor.const I).obj A ⟶ H) ≃ DiagramFamily W H A where
  toFun := diagramExpand
  invFun := diagramDiagonal
  left_inv := diagramDiagonal_expand
  right_inv := diagramExpand_diagonal

end

end SerrePositivity.KST.Spectra.SimplexDensity
