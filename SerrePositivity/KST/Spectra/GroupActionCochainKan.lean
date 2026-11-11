module

public import SerrePositivity.KST.Spectra.FreeActionEndKan
public import SerrePositivity.KST.Spectra.FreeCochainWeight
public import SerrePositivity.KST.Spectra.GroupActionCochainFunctor

/-!
概要：群作用の標準的な余単体 cochain の各値は点つき Kan 複体。
方針：EG_n の自由軌道の表示と、自由作用の end の内部 Hom 表示を合成する。
規約：群の有限性や係数の有理性を仮定しない。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。hG の余単体模型の Kan な各値。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet


namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：群作用の cochain の各次数の基礎単体集合は Kan。
方針：自由作用の同変 end の Kan 性を自由軌道への同型で移す。
規約：任意の群と任意の BF 作用スペクトルについて成立する。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain の通常の Tot の係数。 -/
instance level_kanComplex {G : Type u} [Group G] (A : GroupAction.{u} G) (k : ℕ)
    (j : SimplexCategory) : KanComplex ((level A k).obj j).right := by
  induction j using SimplexCategory.rec with | _ n =>
  let B := (GroupAction.levelFunctor G k).obj A
  let : KanComplex B.V.right := inferInstanceAs (KanComplex (A.V.level k).space.right)
  have h := FreeActionFamily.pointedEnd_kanComplex (Fin n → G) B
  let : KanComplex (PointedSimplicialSet.forget.obj (PointedWeightedEnd.obj
      ((actionWeightFunctor G).obj (Action.leftRegular G ⊗ Action.trivial G (Fin n → G)))
      (AsSmall.down ⋙ (GroupAction.diagramFunctor G).obj A ⋙ OmegaSpectrum.levelEvaluation k))) := h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (PointedSimplicialSet.forget.mapIso (cochainFreeIso A k n).symm)

end

end SerrePositivity.KST.Spectra.GroupActionCochains
