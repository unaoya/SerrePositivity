module

public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimit
public import SerrePositivity.KST.Spectra.PointedWeightedEndFunctor

/-!
概要：Kan 列の homotopy end の射への作用と厳密な関手法則。
方針：各段の点つき end の射を束ね、内部 Hom 交換の自然性で構造条件を示す。
規約：BF 置換前の Kan 列では関手法則を厳密に満たす。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の比較射と係数の自然性。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet


namespace SerrePositivity.KST.Spectra.KanSequence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I] {D E F : I ⥤ KanSequence.{u}}

/-- 概要：図式の自然変換を一段で評価する。
方針：段評価関手を右 whisker する。
規約：添字圏に filtered 条件を課さない。
使われ方：HA §1.4.2。homotopy end の各段の射。 -/
abbrev homotopyLimitLevelTransformation (τ : D ⟶ E) (n : ℕ) :
    levelDiagram D n ⟶ levelDiagram E n :=
  Functor.whiskerRight τ (levelEvaluation n)

/-- 概要：段の随伴構造射の自然変換は係数図式の射に関して自然。
方針：各成分で厳密な Kan 列の射の随伴可換式を使う。
規約：自然変換の厳密な等式。
使われ方：HA §1.4.2、BF 1978 §2。end の列の射の構造条件。 -/
theorem adjointTransformation_natural (τ : D ⟶ E) (n : ℕ) :
    homotopyLimitLevelTransformation τ n ≫ adjointTransformation E n =
      adjointTransformation D n ≫ Functor.whiskerRight
        (homotopyLimitLevelTransformation τ (n + 1)) (ihom PointedSimplicialSet.circle.{u}) := by
  apply NatTrans.ext
  funext i
  exact (τ.app i).adjoint_comm n

/-- 概要：各段の end の射は homotopy end の列の随伴構造射と可換。
方針：係数の随伴自然性を end に送り、loop 交換の自然性で比較する。
規約：通常の点つき射の厳密な等式。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の射への作用。 -/
theorem homotopyLimitMapApp_adjoint (τ : D ⟶ E) (n : ℕ) :
    PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (homotopyLimitLevelTransformation τ n) ≫
      homotopyLimitAdjoint E n =
    homotopyLimitAdjoint D n ≫ (ihom PointedSimplicialSet.circle.{u}).map
      (PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (homotopyLimitLevelTransformation τ (n + 1))) := by
  let A := PointedSimplicialSet.circle.{u}
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I
  let a := PointedWeightedEnd.map W (homotopyLimitLevelTransformation τ n)
  let b := PointedWeightedEnd.map W (homotopyLimitLevelTransformation τ (n + 1))
  let mD := PointedWeightedEnd.map W (adjointTransformation D n)
  let mE := PointedWeightedEnd.map W (adjointTransformation E n)
  let t := PointedWeightedEnd.map W (Functor.whiskerRight
    (homotopyLimitLevelTransformation τ (n + 1)) (ihom A))
  let eD := PointedWeightedEnd.cotensorIso A W (levelDiagram D (n + 1))
  let eE := PointedWeightedEnd.cotensorIso A W (levelDiagram E (n + 1))
  have hn := PointedWeightedEnd.cotensorIso_natural A W
    (homotopyLimitLevelTransformation τ (n + 1))
  change (ihom A).map b ≫ eE.hom = eD.hom ≫ t at hn
  have hm : a ≫ mE = mD ≫ t := by
    change PointedWeightedEnd.map W (homotopyLimitLevelTransformation τ n) ≫
      PointedWeightedEnd.map W (adjointTransformation E n) =
      PointedWeightedEnd.map W (adjointTransformation D n) ≫
        PointedWeightedEnd.map W (Functor.whiskerRight
          (homotopyLimitLevelTransformation τ (n + 1)) (ihom A))
    rw [← PointedWeightedEnd.map_comp, adjointTransformation_natural, PointedWeightedEnd.map_comp]
  apply (cancel_mono eE.hom).mp
  change (a ≫ (mE ≫ eE.inv)) ≫ eE.hom = ((mD ≫ eD.inv) ≫ (ihom A).map b) ≫ eE.hom
  calc
    _ = a ≫ mE := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = mD ≫ t := hm
    _ = _ := by simp only [Category.assoc, hn, Iso.inv_hom_id_assoc]

/-- 概要：Kan 列の図式の射は homotopy end の Kan 列の実際の厳密な射を誘導する。
方針：各段の end の射を束ね、随伴の単射性で構造条件を戻す。
規約：単射構造射の置換前の列で構成する。
使われ方：HA §1.4.2、BF 1978 §2。BF 比較への持ち上げの入力。 -/
def homotopyLimitMap (τ : D ⟶ E) : Hom (homotopyLimit D) (homotopyLimit E) where
  app n := PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (homotopyLimitLevelTransformation τ n)
  comm n := by
    apply (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((homotopyLimit D).level n).space
      ((homotopyLimit E).level (n + 1)).space).injective
    change curry (PointedSimplicialSet.circle.{u} ◁
      PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (homotopyLimitLevelTransformation τ n) ≫
        uncurry (homotopyLimitAdjoint E n)) =
      curry (uncurry (homotopyLimitAdjoint D n) ≫
        PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (homotopyLimitLevelTransformation τ (n + 1)))
    rw [curry_natural_left, curry_uncurry, curry_natural_right, curry_uncurry]
    exact homotopyLimitMapApp_adjoint τ n

/-- 概要：homotopy end の列の射は各段の全基点 π_* 同型を保つ。
方針：段の自然変換に点つき end の同型保存を適用する。
規約：零次数を含み全ての基点で述べる。
使われ方：Goerss–Jardine I §7、HA §1.4.2。hG・Tot の係数の置換不変性。 -/
theorem homotopyLimitMap_levelwise (τ : D ⟶ E)
    (hτ : ∀ i n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((τ.app i).app n).right) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((homotopyLimitMap τ).app n).right :=
  PointedWeightedEnd.map_piIsomorphism (homotopyLimitLevelTransformation τ n) (fun i ↦ hτ i n)

/-- 概要：Kan 列の homotopy end の射への作用は恒等射を保つ。
方針：各段で end の恒等法則を使う。
規約：厳密な Kan 列の射の等式。
使われ方：HA §1.4.2。hG・Tot の関手法則。 -/
theorem homotopyLimitMap_id (D : I ⥤ KanSequence.{u}) :
    homotopyLimitMap (𝟙 D) = 𝟙 (homotopyLimit D) := by
  apply Hom.ext_app
  intro n
  change PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (𝟙 (levelDiagram D n)) = 𝟙 _
  exact PointedWeightedEnd.map_id _ _

/-- 概要：Kan 列の homotopy end の射への作用は合成を保つ。
方針：各段で end の合成法則を使う。
規約：厳密な Kan 列の射の等式。
使われ方：HA §1.4.2、BF 1978 §2。置換前の hG・Tot の関手性。 -/
theorem homotopyLimitMap_comp (τ : D ⟶ E) (υ : E ⟶ F) :
    homotopyLimitMap (τ ≫ υ) = (homotopyLimitMap τ).comp (homotopyLimitMap υ) := by
  apply Hom.ext_app
  intro n
  change PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (homotopyLimitLevelTransformation τ n ≫ homotopyLimitLevelTransformation υ n) =
    PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (homotopyLimitLevelTransformation τ n) ≫
      PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (homotopyLimitLevelTransformation υ n)
  exact PointedWeightedEnd.map_comp _ _ _

end

end SerrePositivity.KST.Spectra.KanSequence
