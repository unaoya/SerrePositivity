module

public import SerrePositivity.KST.Spectra.TwistedKanSequenceNaturality

/-!
概要：自己射と可換する列射を、構造を twist した列の厳密な射へ束ねる。
方針：元の構造可換式と自己射の可換式を合成し、反復比較の自然性を保持する。
規約：Ω 条件や対合性は不要。
使われ方：符号補正を BF 源へ移す一つの厳密な列比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra.KanSequence

/-- 自己射と可換する同じ列射は、twist 後にも厳密な列射を与える。 -/
def twistHom {X Y : KanSequence.{u}} (r : Hom X X) (s : Hom Y Y) (f : Hom X Y)
    (h : ∀ n, r.app n ≫ f.app n = f.app n ≫ s.app n) : Hom (twist r) (twist s) where
  app := f.app
  comm n := by
    change PointedSimplicialSet.circle.{u} ◁ f.app n ≫ (Y.sigma n ≫ s.app (n + 1)) =
      (X.sigma n ≫ r.app (n + 1)) ≫ f.app (n + 1)
    rw [← Category.assoc, f.comm, Category.assoc, ← h, ← Category.assoc]

/-- 源で反復してから twist 後の射を施すと、元の射の後の標的の反復比較に厳密に一致。 -/
lemma twistHom_twistMap_app {X Y : KanSequence.{u}} (r : Hom X X) (s : Hom Y Y)
    (f : Hom X Y) (h : ∀ n, r.app n ≫ f.app n = f.app n ≫ s.app n) (n : ℕ) :
    (twistMap r).app n ≫ (twistHom r s f h).app n =
      f.app n ≫ (twistMap s).app n := twistMap_natural_app r s f h n

end SerrePositivity.KST.Spectra.KanSequence
