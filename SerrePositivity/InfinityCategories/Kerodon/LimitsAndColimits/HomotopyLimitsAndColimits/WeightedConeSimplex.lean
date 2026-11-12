module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRepresentableCoefficients

/-!
概要：反転した表現可能な weighted nerve の simplex から coherent な cone simplex を作る。
方針：初点を固定した x に、後続の頂点を図式に送り、係数評価を非定値 Hom とする。
規約：頂点数は n+2。元の n+1 頂点の図式は succ 側に置く。
使われ方：HTT 4.2.4.1、Kerodon §7.5.4（Tag 03B5） の錐の比較の simplex の組立て。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet SimplicialThickening CartesianMonoidalCategory MonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：cone の初点を x、後続頂点を元の図式の対象へ写す。
方針：Fin.cases の初点と正頂点の分岐を使う。
規約：G は元の n+1 頂点の通常の図式。
使われ方：HTT 4.2.4.1 の cone の豊穣関手の対象の作用。 -/
def weightedConeObj {C : Type v} [Category.{u} C] (x : C) {n : ℕ} (G : Fin (n + 1) ⥤ C)
    (i : Fin (n + 2)) : C :=
  Fin.cases x G.obj i

/-- 概要：正頂点から初点への Hom からは任意の単体集合への空写像がある。
方針：path の端点の不等式は i.succ≤0 となり矛盾する。
規約：単体の次数に関係なく始域は空。
使われ方：HTT 4.2.4.1 の cone の Hom の全ての分岐の定義。 -/
def weightedConeEmptyMap {n : ℕ} (i : Fin (n + 1)) (X : SSet.{u}) :
    nerve (Path (ULift.up i.succ : ULift.{u} (Fin (n + 2))) (ULift.up 0)) ⟶ X where
  app d := ↾fun P ↦ False.elim (by
    have h := Path.le (P.obj 0)
    change i.succ ≤ 0 at h
    simp at h)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro P
    have h := Path.le (P.obj 0)
    change i.succ ≤ 0 at h
    simp at h

/-- 概要：正頂点間の Hom は元の通常の図式の射を定値 simplex として表す。
方針：path の存在による順序から図式の射を選ぶ。
規約：途中の path の頂点の情報を捨てる strict な部分。
使われ方：HTT 4.2.4.1 の元の図式を cone の面として固定する。 -/
noncomputable def weightedConeTailHom {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (G : Fin (n + 1) ⥤ C) (i j : Fin (n + 1)) :
    nerve (Path (ULift.up i.succ : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) ⟶
      SimplicialCategory.sHom (G.obj i) (G.obj j) where
  app d := ↾fun P ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
    (SimplicialCategory.homEquiv' _ _ (G.map (homOfLE
      (Fin.succ_le_succ_iff.mp
        (show i.succ ≤ j.succ from Path.le (J := ULift.{u} (Fin (n + 2))) (P.obj 0)))))) d.unop.len
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro P
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback
      (SimplicialCategory.homEquiv' _ _ (G.map (homOfLE
        (Fin.succ_le_succ_iff.mp
        (show i.succ ≤ j.succ from
          Path.le (J := ULift.{u} (Fin (n + 2))) (P.obj 0)))))) α.unop).symm

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 概要：表現可能な係数の cone の全頂点間の Hom の射。
方針：初点の自己 Hom、係数評価、空の逆向き Hom、通常の図式の Hom に場合分けする。
規約：τ は反転した sHom の初区間の自然変換。
使われ方：HTT 4.2.4.1 の coherent cone の豊穣関手の Hom データ。 -/
noncomputable def weightedConeHom (F : I ⥤ C) (x : C) {n : ℕ}
    {σ : ComposableArrows I n}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)
    (i j : Fin (n + 2)) :
    SimplicialCategory.sHom
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up j⟩ ⟶
    SimplicialCategory.sHom (weightedConeObj x (σ ⋙ F) i)
      (weightedConeObj x (σ ⋙ F) j) := by
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet x
    | succ j => exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ j
  | succ i =>
    induction j using Fin.cases with
    | zero => exact weightedConeEmptyMap i _
    | succ j => exact weightedConeTailHom (σ ⋙ F) i j

/-- 概要：weighted nerve の係数は coherent nerve の初点 x の cone simplex を与える。
方針：定義済みの Hom の作用に単位則と八通りの合成則を確認する。
規約：Kan 性を仮定せず、元の図式の strict な面を持つ simplex を構成する。
使われ方：HTT 4.2.4.1、Kerodon §7.5.4（Tag 03B5） の実際の cone 比較射の各次数。 -/
noncomputable def weightedConeSimplex (F : I ⥤ C) (x : C) {n : ℕ}
    {σ : ComposableArrows I n}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) :
    (SimplicialNerve C) _⦋n + 1⦌ where
  obj i := weightedConeObj x (σ ⋙ F) i.as.down
  map i j := weightedConeHom F x τ i.as.down j.as.down
  map_id := by
    rintro ⟨⟨i⟩⟩
    induction i using Fin.cases with
    | zero =>
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    | succ i =>
      apply SSet.hom_ext
      rintro ⟨⟨d⟩⟩
      apply ConcreteCategory.hom_ext
      intro a
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (SimplicialCategory.homEquiv' _ _ ((σ ⋙ F).map (𝟙 i))) d =
          (eId SSet (F.obj (σ.obj i))).app (Opposite.op ⦋d⦌) a
      rw [CategoryTheory.Functor.map_id]
      have ha : a = PUnit.unit := @Subsingleton.elim PUnit inferInstance _ _
      subst a
      simp only [SimplicialCategory.homEquiv', Equiv.trans_apply, eHomEquiv_id]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.unitHom_app_constant (eId SSet ((σ ⋙ F).obj i)) d).symm
  map_comp := by
    rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨k⟩⟩
    induction i using Fin.cases <;> induction j using Fin.cases <;>
      induction k using Fin.cases
    all_goals
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      rintro ⟨P, Q⟩
    case zero.zero.zero =>
      change (eId SSet x).app d PUnit.unit =
        (eComp SSet x x x).app d
          ((eId SSet x).app d PUnit.unit, (eId SSet x).app d PUnit.unit)
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app x x d _).symm
    case zero.zero.succ k =>
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ k).app d
        ((eComp SSet
          (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
          ⟨ULift.up 0⟩ ⟨ULift.up k.succ⟩).app d (P, Q)) =
        (eComp SSet x x (F.obj (σ.obj k))).app d
          ((eId SSet x).app d PUnit.unit, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ k).app d Q)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app]
      congr 1
      apply CategoryTheory.Functor.ext (fun t ↦ ?_)
      have hp : P.obj t = 𝟙 (⟨ULift.up 0⟩ : SimplicialThickening
          (ULift.{u} (Fin (n + 2)))) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.thickeningPath_end_eq_id _ _
      change P.obj t ≫ Q.obj t = Q.obj t
      rw [hp, Category.id_comp]
    case zero.succ.zero j =>
      have h := Path.le (Q.obj 0)
      change j.succ ≤ 0 at h
      simp at h
    case zero.succ.succ j k =>
      have h : j ≤ k := Fin.succ_le_succ_iff.mp
        (show j.succ ≤ k.succ from Path.le (J := ULift.{u} (Fin (n + 2))) (Q.obj 0))
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedRepresentableCoefficient_comp F x τ j k h d P Q
    case succ.zero.zero i =>
      have h := Path.le (P.obj 0)
      change i.succ ≤ 0 at h
      simp at h
    case succ.zero.succ i k =>
      have h := Path.le (P.obj 0)
      change i.succ ≤ 0 at h
      simp at h
    case succ.succ.zero i j =>
      have h := Path.le (Q.obj 0)
      change j.succ ≤ 0 at h
      simp at h
    case succ.succ.succ i j k =>
      rcases d with ⟨⟨d⟩⟩
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _
        ((σ ⋙ F).map (homOfLE _))) d =
        (SimplicialCategory.sHomComp ((σ ⋙ F).obj i)
          ((σ ⋙ F).obj j) ((σ ⋙ F).obj k)).app (Opposite.op ⦋d⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _
            ((σ ⋙ F).map (homOfLE _))) d,
           _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _
            ((σ ⋙ F).map (homOfLE _))) d)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_constant_comp, ← CategoryTheory.Functor.map_comp]
      rfl


/-- 概要：組み立てた cone simplex の初点は x の標準頂点。
方針：初点への制限は全 Hom を豊穣恒等へ送ることを確認する。
規約：零単体への制限を元の nerve の写像として明示する。
使われ方：HTT 4.2.4.1 の左 coslice の固定頂点条件。 -/
lemma weightedConeSimplex_apex (F : I ⥤ C) (x : C) {n : ℕ}
    {σ : ComposableArrows I n}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) :
    (SimplicialNerve C).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
      (weightedConeSimplex F x τ) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) (fun i j ↦ ?_)
  change (_ ≫ SemiCartesianMonoidalCategory.toUnit _) ≫ eId SSet x ≫
    eqToHom (rfl : SimplicialCategory.sHom x x = _) =
      SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet x
  simp only [comp_toUnit, eqToHom_refl, Category.comp_id]

/-- 概要：組み立てた cone simplex の初点以外の面は元の strict な図式。
方針：正頂点間の定値 Hom の作用を通常の図式の coherent 表示と比較する。
規約：δ 0 が cone の底の面。
使われ方：HTT 4.2.4.1 の底の図式を保つ条件。 -/
lemma weightedConeSimplex_tail (F : I ⥤ C) (x : C) {n : ℕ}
    {σ : ComposableArrows I n}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) :
    (SimplicialNerve C).δ 0 (weightedConeSimplex F x τ) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F).app (Opposite.op ⦋n⦌) (ULift.up σ) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) (fun i j ↦ ?_)
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

/-- 概要：cone simplex の構成は初点固定の全ての添字変換と可換。
方針：Hom の四分岐で係数の自然性と定値射の合成を使う。
規約：元の図式を α で制限し、初点には prependOrderHom の拡張を使う。
使われ方：HTT 4.2.4.1 の実際の左 coslice 射の単体的自然性。 -/
lemma weightedConeSimplex_reindex (F : I ⥤ C) (x : C) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) {σ : ComposableArrows I n}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) :
    (SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom).uliftMap).comp SSet
      (weightedConeSimplex F x τ) =
    weightedConeSimplex F x
      (σ := (SimplexCategory.toCat.map α).toFunctor ⋙ σ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction.{u} α ≫
        CategoryTheory.Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor τ) := by
  refine EnrichedFunctor.ext SSet (fun i ↦ ?_) (fun i j ↦ ?_)
  · rcases i with ⟨⟨i⟩⟩
    induction i using Fin.cases <;> rfl
  · rcases i with ⟨⟨i⟩⟩
    rcases j with ⟨⟨j⟩⟩
    induction i using Fin.cases <;> induction j using Fin.cases
    all_goals
      simp only [eqToHom_refl, Category.comp_id]
    case zero.zero =>
      change (_ ≫ SemiCartesianMonoidalCategory.toUnit _) ≫ eId SSet x =
        SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet x
      rw [comp_toUnit]
    case zero.succ j =>
      change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindexFunctor α.toOrderHom j) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ (α.toOrderHom j) = _
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient_reindex α τ j
    case succ.zero i =>
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      have h := Path.le (P.obj 0)
      change i.succ ≤ 0 at h
      simp at h
    case succ.succ i j =>
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
