module

public import SerrePositivity.KST.Spectra.KanSequenceCategory
public import Mathlib.CategoryTheory.Limits.Cones

/-!
概要：Kan 列の指定した錐の極限性を、各段の点つき極限から証明する。
方針：段ごとの普遍射を取り、極限の射影で構造可換性と一意性を検査する。
規約：元の錐の頂点の Kan 性は対象に含まれる。使われ方：重み付き end の厳密な普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory
namespace SerrePositivity.KST.Spectra.KanSequence
variable {I : Type v} [Category.{w} I] {D : I ⥤ KanSequence.{u}}

/-- 段ごとの極限錐への普遍射は、実際の Kan 列の厳密な射をなす。 -/
def liftOfLevelLimits (c : Cone D) (hc : ∀ n, IsLimit ((levelEvaluation n).mapCone c))
    (s : Cone D) : s.pt ⟶ c.pt where
  app n := (hc n).lift ((levelEvaluation n).mapCone s)
  comm n := by
    have hf (k : ℕ) (i : I) :
        (hc k).lift ((levelEvaluation k).mapCone s) ≫ (c.π.app i).app k =
          (s.π.app i).app k := (hc k).fac _ i
    apply (hc (n + 1)).hom_ext
    intro i
    have hcomm : PointedSimplicialSet.circle.{u} ◁ (c.π.app i).app n ≫ (D.obj i).sigma n =
        c.pt.sigma n ≫ (c.π.app i).app (n + 1) := (c.π.app i).comm n
    change (PointedSimplicialSet.circle.{u} ◁
        (hc n).lift ((levelEvaluation n).mapCone s) ≫ c.pt.sigma n) ≫
          (c.π.app i).app (n + 1) =
      (s.pt.sigma n ≫ (hc (n + 1)).lift ((levelEvaluation (n + 1)).mapCone s)) ≫
        (c.π.app i).app (n + 1)
    rw [Category.assoc, ← hcomm, ← Category.assoc,
      ← whiskerLeft_comp, hf n i, Category.assoc, hf (n + 1) i]
    exact (s.π.app i).comm n

/-- 各段で実際の点つき極限である錐は、Kan 列の圏でも実際の極限である。 -/
def isLimitOfLevelLimits (c : Cone D) (hc : ∀ n, IsLimit ((levelEvaluation n).mapCone c)) :
    IsLimit c where
  lift := liftOfLevelLimits c hc
  fac s i := by
    apply Hom.ext_app
    intro n
    exact (hc n).fac ((levelEvaluation n).mapCone s) i
  uniq s m hm := by
    apply Hom.ext_app
    intro n
    apply (hc n).hom_ext
    intro i
    have h := congrArg (fun f : s.pt ⟶ D.obj i ↦ f.app n) (hm i)
    exact h.trans ((hc n).fac ((levelEvaluation n).mapCone s) i).symm

end SerrePositivity.KST.Spectra.KanSequence
