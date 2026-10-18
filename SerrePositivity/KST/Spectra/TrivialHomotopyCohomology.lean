module

public import SerrePositivity.KST.Spectra.TrivialHomotopyCochainComplex
public import SerrePositivity.KST.Spectra.RationalCochainCohomology
public import SerrePositivity.KST.Spectra.ZeroCochainCohomology
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
概要：自明な Kan 作用の高次 π_* の cochain のコホモロジーの具体的な計算。
方針：指定した線形係数の cochain の計算を加法群への忘却と実際の複体比較で移す。
規約：指定係数の加群構造を仮定する。Tot のホモトピー群はまだ計算しない。
使われ方：Goerss–Jardine VIII §2。有理 Shapiro の Tot の計算に必要な cochain 消滅の入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra.TrivialHomotopyCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance trivialCohomologyUnderlyingKan (G : Type u) [Group G]
    (X : PointedSimplicialSet.{u}) [KanComplex X.right] : KanComplex (Action.trivial G X).V.right :=
  inferInstanceAs (KanComplex X.right)

/-- 概要：自明な Kan 作用の高次 π_* の cochain の零次数コホモロジーは係数そのもの。
方針：線形係数の零次数の計算を加法群に忘却し、複体の比較で戻す。
規約：q はホモトピー次数 q+2。群の有限性は不要。
使われ方：Goerss–Jardine VIII §2。有理 cochain で残る零次数の表示。 -/
def zeroCohomologyIso (X : PointedSimplicialSet.{u}) [KanComplex X.right]
    (R G : Type u) [CommRing R] [Group G] (q : ℕ) [Module R (coefficient X q)] :
    (KanHomotopyGroup.cochainComplex
      (PointedActionCochains.obj (Action.trivial G X)) q).homology 0 ≅
        AddCommGrpCat.of (coefficient X q) :=
  cohomologyIso X R G q 0 ≪≫
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapIso
      (LinearGroupCochains.zeroCohomologyIsoOfTrivial (Rep.trivial R G (coefficient X q)))

/-- 概要：有限群の自明な Kan 作用の高次 π_* の cochain の正次数コホモロジーは零。
方針：標数零の体の係数の群コホモロジー消滅を複体と忘却の比較で移す。
規約：q はホモトピー次数 q+2。指定した係数体の加群構造を仮定する。
使われ方：Goerss–Jardine VIII §2。Tot の π_* 計算への正次数 cochain 消滅の入力。 -/
theorem positive_cohomology_isZero (X : PointedSimplicialSet.{u}) [KanComplex X.right]
    (R G : Type u) [Field R] [CharZero R] [Group G] [Finite G]
    (q n : ℕ) [Module R (coefficient X q)] :
    IsZero ((KanHomotopyGroup.cochainComplex
      (PointedActionCochains.obj (Action.trivial G X)) q).homology (n + 1)) := by
  have h := LinearGroupCochains.positive_cohomology_isZero
    (Rep.trivial R G (coefficient X q)) n
  have hf := (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map_isZero h
  exact hf.of_iso (cohomologyIso X R G q (n + 1))

end

end SerrePositivity.KST.Spectra.TrivialHomotopyCochains
