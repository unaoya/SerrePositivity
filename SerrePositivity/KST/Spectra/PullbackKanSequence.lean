module
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PullbackKanSequence

public import SerrePositivity.KST.Spectra.KanSequence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：段ごとの Kan fibration に沿う Kan 列の引き戻し。
方針：点つき圏で段ごとに引き戻し、構造射を普遍性で貼る。
規約：構造射の単射性や Ω 条件はここでは主張しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。mapping path 列。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : PointedSimplicialSet.forget.{u}.IsRightAdjoint :=
  PointedObject.adjoinForgetAdjunction.isRightAdjoint

namespace KanSequence

variable {E X B : KanSequence.{u}} (f : Hom E B) (g : Hom X B)

/-- 概要：引き戻しの段の suspension 構造射。
方針：二つの射影の suspension と元の構造射を引き戻しの普遍性で貼る。
規約：各段の Kan 性は構造射の構成そのものには不要。
使われ方：BF 1978 §2、HTT A.3.3。mapping path 列の構造。 -/
def pullbackSigma (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (pullback (f.app n) (g.app n)) ⟶
      pullback (f.app (n + 1)) (g.app (n + 1)) :=
  pullback.lift (PointedSimplicialSet.circle.{u} ◁ pullback.fst (f.app n) (g.app n) ≫ E.sigma n)
    (PointedSimplicialSet.circle.{u} ◁ pullback.snd (f.app n) (g.app n) ≫ X.sigma n) (by
      rw [Category.assoc, ← f.comm n, ← Category.assoc, ← whiskerLeft_comp,
        pullback.condition, whiskerLeft_comp, Category.assoc, g.comm n, ← Category.assoc])

variable [hf : ∀ n, Fibration (f.app n).right]

/-- 概要：段ごとの Kan fibration に沿う Kan 列の引き戻し。
方針：点つき引き戻しの各段と構成済みの構造射を束ねる。
規約：Ω 条件を入力にも出力の主張にも含めない。
使われ方：BF 1978 §2、Goerss–Jardine I §7。mapping path 列。 -/
def pullbackSequence : KanSequence.{u} where
  level n := {
    space := pullback (f.app n) (g.app n)
    kan := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_kanComplex _ _ }
  sigma := pullbackSigma f g

/-- 概要：引き戻しの Kan 列から第一の列への厳密な射影。
方針：引き戻しの第一射影を各段で使う。
規約：構造射との可換性は引き戻しの計算式。
使われ方：BF 1978 §2。mapping path の path 成分。 -/
def pullbackFirst : Hom (pullbackSequence f g) E where
  app n := pullback.fst (f.app n) (g.app n)
  comm n := by
    change _ = pullbackSigma f g n ≫ pullback.fst _ _
    simp only [pullbackSigma, pullback.lift_fst]

/-- 概要：引き戻しの Kan 列から第二の列への厳密な射影。
方針：引き戻しの第二射影を各段で使う。
規約：構造射との可換性は引き戻しの計算式。
使われ方：BF 1978 §2。mapping path の元の源への比較射。 -/
def pullbackSecond : Hom (pullbackSequence f g) X where
  app n := pullback.snd (f.app n) (g.app n)
  comm n := by
    change _ = pullbackSigma f g n ≫ pullback.snd _ _
    simp only [pullbackSigma, pullback.lift_snd]

/-- 概要：二つの厳密な列の射から引き戻し列への厳密な射を作る。
方針：各段を引き戻しへ持ち上げ、構造条件を両射影の後で確認する。
規約：二つの合成の一致を各段で要求する。
使われ方：BF 1978 §2、HTT A.3.3。mapping path の比較射。 -/
def pullbackLift {T : KanSequence.{u}} (a : Hom T E) (b : Hom T X)
    (h : ∀ n, a.app n ≫ f.app n = b.app n ≫ g.app n) :
    Hom T (pullbackSequence f g) where
  app n := pullback.lift (a.app n) (b.app n) (h n)
  comm n := by
    apply pullback.hom_ext
    · change (PointedSimplicialSet.circle.{u} ◁ pullback.lift (a.app n) (b.app n) (h n) ≫
        pullbackSigma f g n) ≫ pullback.fst _ _ =
          (T.sigma n ≫ pullback.lift (a.app (n + 1)) (b.app (n + 1)) (h (n + 1))) ≫
            pullback.fst _ _
      simp only [Category.assoc, pullbackSigma, pullback.lift_fst,
        ← whiskerLeft_comp_assoc, a.comm n]
    · change (PointedSimplicialSet.circle.{u} ◁ pullback.lift (a.app n) (b.app n) (h n) ≫
        pullbackSigma f g n) ≫ pullback.snd _ _ =
          (T.sigma n ≫ pullback.lift (a.app (n + 1)) (b.app (n + 1)) (h (n + 1))) ≫
            pullback.snd _ _
      simp only [Category.assoc, pullbackSigma, pullback.lift_snd,
        ← whiskerLeft_comp_assoc, b.comm n]

end KanSequence

end

end SerrePositivity.KST.Spectra
