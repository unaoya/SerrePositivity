module

public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimit
public import SerrePositivity.KST.Spectra.PointedWeightedConeCompatibility

/-!
概要：Kan 列の厳密な錐から段ごとの homotopy end への厳密な列の射。
方針：各段の定数族の比較を使い、随伴構造射との整合性を loop 交換で確認する。
規約：錐の始域の単射構造射や Ω 条件は不要。
使われ方：HA §1.4.2、BF 1978 §2。自明作用から hG への実際の標準射の置換前の構成。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet


namespace SerrePositivity.KST.Spectra.KanSequence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I] {D : I ⥤ KanSequence.{u}}

/-- 概要：Kan 列の錐を指定した段で評価する。
方針：段評価関手で錐を移す。
規約：厳密な点つき図式の錐。
使われ方：HA §1.4.2。段ごとの標準比較の入力。 -/
def levelCone (c : Cone D) (n : ℕ) : Cone (levelDiagram D n) :=
  (levelEvaluation n).mapCone c

/-- 概要：厳密な錐から homotopy end の列への各段の標準比較。
方針：基点を保つ定数族の end への比較射を適用する。
規約：点つき射の実際の族。
使われ方：HA §1.4.2、BF 1978 §2。標準射を列に束ねる各段の射。 -/
def homotopyLimitConeApp (c : Cone D) (n : ℕ) :
    (c.pt.level n).space ⟶ ((homotopyLimit D).level n).space :=
  PointedWeightedEnd.coneComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelCone c n)

/-- 概要：錐から homotopy end への比較は随伴構造射と厳密に可換。
方針：錐の自然性を end に送り、内部 Hom と end の交換で標準比較を移す。
規約：元の Kan 列の射の構造条件だけを使う。
使われ方：HA §1.4.2、BF 1978 §2。厳密な列の射の構造条件。 -/
theorem homotopyLimitConeApp_adjoint (c : Cone D) (n : ℕ) :
    homotopyLimitConeApp c n ≫ homotopyLimitAdjoint D n =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (c.pt.level n).space (c.pt.level (n + 1)).space (c.pt.sigma n) ≫
        (ihom PointedSimplicialSet.circle.{u}).map (homotopyLimitConeApp c (n + 1)) := by
  let A := PointedSimplicialSet.circle.{u}
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I
  let a := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (c.pt.level n).space (c.pt.level (n + 1)).space (c.pt.sigma n)
  let e := PointedWeightedEnd.cotensorIso A W (levelDiagram D (n + 1))
  have h := PointedWeightedEnd.coneComparison_natural W (levelCone c n)
    ((ihom A).mapCone (levelCone c (n + 1))) a (adjointTransformation D n)
    (fun i ↦ ((c.π.app i).adjoint_comm n).symm)
  have ht := PointedWeightedEnd.coneComparison_cotensor A W (levelCone c (n + 1))
  change (ihom A).map (homotopyLimitConeApp c (n + 1)) ≫ e.hom = _ at ht
  change a ≫ PointedWeightedEnd.coneComparison W ((ihom A).mapCone
    (levelCone c (n + 1))) = homotopyLimitConeApp c n ≫
      PointedWeightedEnd.map W (adjointTransformation D n) at h
  apply (cancel_mono e.hom).mp
  change (homotopyLimitConeApp c n ≫
      (PointedWeightedEnd.map W (adjointTransformation D n) ≫ e.inv)) ≫ e.hom =
    (a ≫ (ihom A).map (homotopyLimitConeApp c (n + 1))) ≫ e.hom
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, ht]
  exact h.symm

/-- 概要：厳密な Kan 列の錐から homotopy end の列への実際の厳密な射。
方針：各段の比較を束ね、随伴の単射性で構造射の可換性を戻す。
規約：列の構造射の単射性をここでは要求しない。
使われ方：HA §1.4.2、BF 1978 §2。BF 比較へ持ち上げる標準射。 -/
def homotopyLimitCone (c : Cone D) : Hom c.pt (homotopyLimit D) where
  app := homotopyLimitConeApp c
  comm n := by
    apply (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (c.pt.level n).space ((homotopyLimit D).level (n + 1)).space).injective
    change curry (PointedSimplicialSet.circle.{u} ◁ homotopyLimitConeApp c n ≫
      uncurry (homotopyLimitAdjoint D n)) = curry (c.pt.sigma n ≫ homotopyLimitConeApp c (n + 1))
    rw [curry_natural_left, curry_uncurry, curry_natural_right]
    exact homotopyLimitConeApp_adjoint c n

end

end SerrePositivity.KST.Spectra.KanSequence
