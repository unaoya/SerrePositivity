module

public import SerrePositivity.InfinityCategories.HomotopyLimits.OppositeFibration
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedHomHolimComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.RepresentableProducts
public import SerrePositivity.InfinityCategories.HomotopyLimits.CospanSingleFibrationComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.TowerComparison
public import SerrePositivity.InfinityCategories.DoldKanComparison.UniverseHomotopy
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：反転した strict Hom 錐の標準比較と coherent な錐の切断模型への合成を構成する。
方針：反転の圏同値で極限性を移し、三形状の Bousfield–Kan 比較を適用する。
規約：係数を反転した比較 q′ を明記し、元の q_x や native な錐の射と同一視しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6 の strict な錐との整合性の証明の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 概要：strict な錐の Hom 錐を単体集合の反転で写した錐。
方針：反転関手の mapCone を実際の Hom 錐へ適用する。
規約：錐の頂点は sHom(x,L).op、係数は H_x ⋙ opFunctor。
使われ方：Kerodon 7.5.4.6 の左 coslice に適合する係数の錐。 -/
noncomputable def reflectedSimplicialHomCone {F : I ⥤ C} (c : Cone F) (x : C) :
    Cone (simplicialHomDiagram F x ⋙ SSet.opFunctor) :=
  SSet.opFunctor.mapCone (simplicialHomCone c x)

/-- 概要：豊穣 Hom 錐の極限性は単体集合の反転で保たれる。
方針：反転の圏同値による極限の保存を適用する。
規約：元の通常の錐の極限性ではなく Hom 錐の極限性を要求する。
使われ方：Kerodon 7.5.3.12 の反転した strict 極限からの比較。 -/
noncomputable def reflectedSimplicialHomCone_isLimit {F : I ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x)) : IsLimit (reflectedSimplicialHomCone c x) := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  exact isLimitOfPreserves SSet.opFunctor hc

/-- 概要：反転した strict Hom 錐から Bousfield–Kan end への標準比較 q′。
方針：反転した実際の錐に重み付き end への標準比較を適用する。
規約：定義には Kan 性も極限性も要求しない。元の q_x とは別の射。
使われ方：HTT 4.2.4.1 の左 coslice の比較と strict な錐の接続。 -/
noncomputable def reflectedRepresentableComparison {F : I ⥤ C} (c : Cone F) (x : C) :
    (SimplicialCategory.sHom x c.pt).op ⟶
      bousfieldKanHolim (simplicialHomDiagram F x ⋙ SSet.opFunctor) :=
  bousfieldKanConeComparison (reflectedSimplicialHomCone c x)

/-- 概要：反転した標準比較 q′ は Hom の始対象について反変自然。
方針：豊穣 Hom の自然性を反転関手で写し、重み付き錐の比較の自然性を使う。
規約：反転した図式の自然変換全体を使い、各点の同値だけで代用しない。
使われ方：HTT 4.2.4.1 の strict な錐に関する表現可能な比較の整合性。 -/
lemma reflectedRepresentableComparison_naturality {F : I ⥤ C} (c : Cone F)
    {x y : C} (f : x ⟶ y) :
    SSet.opFunctor.map (((SimplicialCategory.sHomFunctor C).map f.op).app c.pt) ≫
        reflectedRepresentableComparison c x =
      reflectedRepresentableComparison c y ≫ (bousfieldKanHolimFunctor I).map
        (Functor.whiskerRight (simplicialHomDiagramPre F f) SSet.opFunctor) := by
  apply weightedConeComparison_naturality (bousfieldKanWeight I)
    (reflectedSimplicialHomCone c y) (reflectedSimplicialHomCone c x)
    (SSet.opFunctor.map (((SimplicialCategory.sHomFunctor C).map f.op).app c.pt))
    (Functor.whiskerRight (simplicialHomDiagramPre F f) SSet.opFunctor)
  intro i
  change SSet.opFunctor.map (((SimplicialCategory.sHomFunctor C).map f.op).app c.pt) ≫
      SSet.opFunctor.map
        (((SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).map (c.π.app i)) =
    SSet.opFunctor.map
        (((SimplicialCategory.sHomFunctor C).obj (Opposite.op y)).map (c.π.app i)) ≫
      SSet.opFunctor.map (((SimplicialCategory.sHomFunctor C).map f.op).app (F.obj i))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  apply SSet.opFunctor.congr_map
  exact (((SimplicialCategory.sHomFunctor C).map f.op).naturality
    (show c.pt ⟶ F.obj i from c.π.app i)).symm

/-- 概要：反転した豊穣積の標準比較 q′ は厳密な同型。
方針：反転した極限錐へ終対象の重みの比較を適用する。
規約：添字の有限性も Kan 性も要求しない。
使われ方：Kerodon 7.5.4.6 の積の strict な錐の比較。 -/
lemma reflectedRepresentableComparison_discrete_isIso {J : Type u}
    {F : Discrete J ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x)) :
    IsIso (reflectedRepresentableComparison c x) :=
  weightedConeComparison_isIso_of_isTerminalWeight _ discreteBousfieldKanWeight_isTerminal
    (reflectedSimplicialHomCone c x) (reflectedSimplicialHomCone_isLimit c x hc)

/-- 概要：一脚が fibration の豊穣 cospan の反転した標準比較 q′ は同値。
方針：反転による極限性・Kan 性・fibration 性の保存を既存の cospan 比較へ渡す。
規約：中央と右端の Kan 性、左脚の fibration 性だけを要求する。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の引き戻しの strict な錐の比較。 -/
lemma reflectedRepresentableComparison_cospan_homotopyEquivalence
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x))
    [KanComplex ((simplicialHomDiagram F x).obj (AsSmall.up.obj .one))]
    [KanComplex ((simplicialHomDiagram F x).obj (AsSmall.up.obj .right))]
    [Fibration ((simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    IsSimplicialHomotopyEquivalence (reflectedRepresentableComparison c x) := by
  have : KanComplex ((simplicialHomDiagram F x ⋙ SSet.opFunctor).obj
      (AsSmall.up.obj .one)) :=
    inferInstanceAs (KanComplex ((simplicialHomDiagram F x).obj (AsSmall.up.obj .one)).op)
  have : KanComplex ((simplicialHomDiagram F x ⋙ SSet.opFunctor).obj
      (AsSmall.up.obj .right)) :=
    inferInstanceAs (KanComplex ((simplicialHomDiagram F x).obj (AsSmall.up.obj .right)).op)
  have : Fibration ((simplicialHomDiagram F x ⋙ SSet.opFunctor).map
      (AsSmall.up.map WalkingCospan.Hom.inl)) := fibration_opFunctor_map _
  exact bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence _
    (reflectedSimplicialHomCone c x) (reflectedSimplicialHomCone_isLimit c x hc)

/-- 概要：豊穣 Hom が fibration の塔をなすとき反転した標準比較 q′ は同値。
方針：反転した Hom 錐の極限性と全隣接遷移の fibration 性を塔の比較へ渡す。
規約：零段の Kan 性と隣接遷移の fibration 性を要求する。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の塔の strict な錐の比較。 -/
lemma reflectedRepresentableComparison_tower_homotopyEquivalence
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x))
    [KanComplex ((simplicialHomDiagram F x).obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    IsSimplicialHomotopyEquivalence (reflectedRepresentableComparison c x) := by
  have : KanComplex ((simplicialHomDiagram F x ⋙ SSet.opFunctor).obj
      (AsSmall.up.obj (Opposite.op 0))) := inferInstanceAs
    (KanComplex ((simplicialHomDiagram F x).obj (AsSmall.up.obj (Opposite.op 0))).op)
  have : ∀ n : ℕ, Fibration ((simplicialHomDiagram F x ⋙ SSet.opFunctor).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)) := fun _ ↦ fibration_opFunctor_map _
  exact bousfieldKanConeComparison_tower_homotopyEquivalence
    (reflectedSimplicialHomCone c x) (reflectedSimplicialHomCone_isLimit c x hc)

/-- 概要：反転した strict Hom の頂点から coherent な錐の切断模型への実際の合成。
方針：q′ を ULift で写し、反転した end からの既存の切断比較へ合成する。
規約：native な錐の Hom 比較との一致はこの定義の結論に含めない。
使われ方：HTT 4.2.4.1 の strict な錐との整合性の検証対象。 -/
noncomputable def reflectedStrictConeSectionsComparison {F : I ⥤ C}
    (c : Cone F) (x : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op ⟶
      coherentConeSectionSpace (strictCoherentDiagram F) (coherentNerveVertex x) :=
  (SSet.uliftFunctor.{v, u}).map (reflectedRepresentableComparison c x) ≫
    reflectedHomHolimConeComparison F x

/-- 概要：豊穣積の反転した strict Hom から切断模型への実際の合成は同値。
方針：q′ の同型性と反転した end の切断比較の同値性を合成する。
規約：局所 Kan 性と Hom 錐の極限性を要求し、離散添字の有限性は不要。
使われ方：HTT 4.2.4.1 の積の strict な錐の比較の入力。 -/
lemma reflectedStrictConeSectionsComparison_discrete_homotopyEquivalence {J : Type u}
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : Discrete J ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x)) :
    IsSimplicialHomotopyEquivalence (reflectedStrictConeSectionsComparison c x) := by
  have : ∀ i, KanComplex ((simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  have := bousfieldKanHolim_kanComplex (simplicialHomDiagram F x ⋙ SSet.opFunctor)
  have := reflectedRepresentableComparison_discrete_isIso c x hc
  exact (DoldKanComparison.ulift_homotopyEquivalence
    (homotopyEquivalence_of_isIso (reflectedRepresentableComparison c x))).comp
      (reflectedHomHolimConeComparison_discrete_homotopyEquivalence F x)

/-- 概要：豊穣 cospan の反転した strict Hom から切断模型への実際の合成は同値。
方針：一脚の fibration 条件による q′ の同値性と切断比較の同値性を合成する。
規約：局所 Kan 性、Hom 錐の極限性、Hom の左脚の fibration 性を要求する。
使われ方：HTT 4.2.4.1 の引き戻しの strict な錐の比較の入力。 -/
lemma reflectedStrictConeSectionsComparison_cospan_homotopyEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x))
    [Fibration ((simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    IsSimplicialHomotopyEquivalence (reflectedStrictConeSectionsComparison c x) := by
  have : ∀ i, KanComplex ((simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  have := bousfieldKanHolim_kanComplex (simplicialHomDiagram F x ⋙ SSet.opFunctor)
  exact (DoldKanComparison.ulift_homotopyEquivalence
    (reflectedRepresentableComparison_cospan_homotopyEquivalence c x hc)).comp
      (reflectedHomHolimConeComparison_cospan_homotopyEquivalence F x)

/-- 概要：豊穣塔の反転した strict Hom から切断模型への実際の合成は同値。
方針：隣接遷移の fibration 条件による q′ の同値性と切断比較の同値性を合成する。
規約：局所 Kan 性、Hom 錐の極限性、全隣接遷移の fibration 性を要求する。
使われ方：HTT 4.2.4.1 の塔の strict な錐の比較の入力。 -/
lemma reflectedStrictConeSectionsComparison_tower_homotopyEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x))
    [∀ n : ℕ, Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    IsSimplicialHomotopyEquivalence (reflectedStrictConeSectionsComparison c x) := by
  have : ∀ i, KanComplex ((simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  have := bousfieldKanHolim_kanComplex (simplicialHomDiagram F x ⋙ SSet.opFunctor)
  exact (DoldKanComparison.ulift_homotopyEquivalence
    (reflectedRepresentableComparison_tower_homotopyEquivalence c x hc)).comp
      (reflectedHomHolimConeComparison_tower_homotopyEquivalence F x)

end SerrePositivity.InfinityCategories.HomotopyLimits
