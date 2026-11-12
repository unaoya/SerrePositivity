module

public import SerrePositivity.KST.Spectra.PointedActionCochains

/-!
概要：点つき作用の余単体 cochain による全基点 π_* 同型の次数ごとの保存。
方針：自由軌道の end の同型保存を自然な比較同型で移す。
規約：係数の Kan 性だけを使い、群の有限性は不要。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain の Ω 条件と作用の置換比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.PointedActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき同変 π_* 同型は余単体 cochain の各次数でも全基点 π_* 同型。
方針：自由軌道への比較の自然性と自由作用の end の不変性を使う。
規約：零次数の成分集合と全ての基点を含む。
使われ方：Goerss–Jardine VIII §2。作用の cochain の各次数のホモトピー不変性。 -/
lemma map_piIsomorphism {G : Type u} [Group G]
    {B C : Action PointedSimplicialSet.{u} G} [KanComplex B.V.right] [KanComplex C.V.right]
    (τ : B ⟶ C) (hτ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism τ.hom.right) (j : SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (X := ((obj B).obj j).right) (Y := ((obj C).obj j).right)
      ((map τ).app j).right := by
  induction j using SimplexCategory.rec with | _ n =>
  let eB : ((obj B).obj (SimplexCategory.mk n)).right ≅
      (PointedWeightedEnd.obj (FreeActionFamily.weight (Fin n → G))
        (FreeActionFamily.pointedCoefficients B)).right :=
    PointedSimplicialSet.forget.mapIso (freeIso B n)
  let eC : ((obj C).obj (SimplexCategory.mk n)).right ≅
      (PointedWeightedEnd.obj (FreeActionFamily.weight (Fin n → G))
        (FreeActionFamily.pointedCoefficients C)).right :=
    PointedSimplicialSet.forget.mapIso (freeIso C n)
  have hfree := FreeActionFamily.pointedEndMap_piIsomorphism (Fin n → G) τ hτ
  have he := congrArg (fun t ↦ t.right) (freeIso_natural τ n)
  change ((map τ).app (SimplexCategory.mk n)).right ≫ eC.hom =
    eB.hom ≫ (PointedWeightedEnd.map (FreeActionFamily.weight (Fin n → G))
      (FreeActionFamily.pointedCoefficientsMap τ)).right at he
  have hc : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (((map τ).app (SimplexCategory.mk n)).right ≫ eC.hom) := by
    rw [he]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso eB).comp hfree
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp hc (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso eC)

end

end SerrePositivity.KST.Spectra.PointedActionCochains
