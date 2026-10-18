module

public import SerrePositivity.KST.Spectra.SimplexDensityEquiv

/-!
概要：標準単体上の密度の族の重み・係数・パラメーターへの自然性。
方針：族の各成分を前後合成し、展開と対角評価の具体式を使う。
規約：全て厳密な射の等式。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。図式上の end への密度比較の移送。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet Opposite

namespace SerrePositivity.KST.Spectra.SimplexDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S T A A' Y Z : SSet.{u}}

/-- 概要：密度の族のパラメーターを前合成する。
方針：各次数で直積の右因子の射を前合成する。
規約：重みと係数は固定する。
使われ方：Goerss–Jardine VIII §1。Hom の同値のパラメーターへの自然性。 -/
def Family.preParameter (s : Family S A Y) (f : A' ⟶ A) : Family S A' Y where
  app n := (_ ◁ (_ ◁ f)) ≫ s.app n
  condition g k x α a := s.condition g k x α (f.app k a)

lemma diagonal_preParameter (s : Family S A Y) (f : A' ⟶ A) :
    diagonal S A' Y (s.preParameter f) = (S ◁ f) ≫ diagonal S A Y s := by
  ext k x
  rfl

/-- 概要：密度の族の係数を後合成する。
方針：各次数で係数の射を後合成する。
規約：重みとパラメーターは固定する。
使われ方：Goerss–Jardine VIII §1。係数図式への密度比較の自然性。 -/
def Family.postCoefficient (s : Family S A Y) (g : Y ⟶ Z) : Family S A Z where
  app n := s.app n ≫ g
  condition f k x α a := congrArg (g.app k) (s.condition f k x α a)

lemma diagonal_postCoefficient (s : Family S A Y) (g : Y ⟶ Z) :
    diagonal S A Z (s.postCoefficient g) = diagonal S A Y s ≫ g := by
  ext k x
  rfl

/-- 概要：密度の族の重みを前合成する。
方針：各次数の単体の射を離散化して族に前合成する。
規約：単体の次数との可換性は重みの射の自然性から従う。
使われ方：Goerss–Jardine VIII §1。添字圏の射への整合条件。 -/
def Family.preWeight (s : Family T A Y) (f : S ⟶ T) : Family S A Y where
  app n := ((Functor.const (SimplexCategoryᵒᵖ)).map (f.app (op n)) ▷ _) ≫ s.app n
  condition g k x α a := by
    change (s.app _).app k (f.app _ (S.map g.op x), (α, a)) =
      (s.app _).app k (f.app _ x, ((SSet.stdSimplex.map g).app k α, a))
    have h := congr($(f.naturality g.op) x)
    change f.app _ (S.map g.op x) = T.map g.op (f.app _ x) at h
    rw [h]
    exact s.condition g k (f.app _ x) α a

lemma diagonal_preWeight (s : Family T A Y) (f : S ⟶ T) :
    diagonal S A Y (s.preWeight f) = (f ▷ A) ≫ diagonal T A Y s := by
  ext k x
  rfl

end

end SerrePositivity.KST.Spectra.SimplexDensity
