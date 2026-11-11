module
public import SerrePositivity.KST.SConstruction.EquivalenceDiagramStableModel
public import SerrePositivity.KST.SConstruction.GappedPushoutPreservation
public import SerrePositivity.KST.SConstruction.GappedIso

/-! # 全同値図式の包含と点ごとの gapped 条件
概要：全同値図式の包含の完全性と、関手圏の gapped 条件の点ごとの判定を証明する。
方針：評価と定数図式による関手同型で完全性を移し、関手圏の普遍性を各点で調べる。
規約：標的は安定な quasicategory。使われ方：object S と core S の行の対応。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：零対象と全押し出しの保存は関手同型で移る。
方針：零頂点での評価と正方形での前合成により普遍性を移す。
規約：標的だけ quasicategory。使われ方：全同値図式の包含の完全性。 -/
lemma PreservesSConstructionData.of_functorIso {A B : SSet.{u}} [Quasicategory B]
    {f g : A ⟶ B} (hf : PreservesSConstructionData f) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    PreservesSConstructionData g := by
  constructor
  · intro z hz
    have ez := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at ez
    exact (hf.1 z hz).of_vertexIso ez
  · intro F hF
    exact IsPushoutSquare.of_functorIso (hf.2 F hF) (e.precomp F)

/-- 概要：安定な標的への関手圏の各評価は零対象と全押し出しを保つ。
方針：零対象と押し出しの点ごとの定理を使う。
規約：添字は任意。使われ方：gapped 条件の点ごとの必要性。 -/
lemma evaluateFunctorAt_preservesSConstructionData {K C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (k : K _⦋0⦌) :
    PreservesSConstructionData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) k) :=
  ⟨fun _ hz => isZeroVertex_evaluateFunctorAt hz k,
    fun F hF => (functor_pushout_iff_pointwise F).1 hF k⟩

/-- 概要：定数関手を指定点で評価すると恒等射。
方針：全同値図式を経由する定数図式の切断の式を使う。
規約：quasicategory 性は不要。使われ方：定数関手の完全性の点ごとの証明。 -/
lemma constantFunctor_evaluation {K C : SSet.{u}} (k : K _⦋0⦌) :
    curry (snd K C) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k = 𝟙 C := by
  rw [← equivalenceDiagramConstant_ι K C, Category.assoc]
  exact equivalenceDiagramConstant_evaluation K C k

/-- 概要：安定な標的の定数関手への包含は零対象と全押し出しを保つ。
方針：各評価との合成が恒等射であることを使う。
規約：添字の空性にも制限しない。使われ方：全同値図式の包含との自然同値。 -/
lemma constantFunctor_preservesSConstructionData (K C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : PreservesSConstructionData (curry (snd K C)) := by
  constructor
  · intro z hz
    apply isZeroVertex_of_pointwise
    intro k
    have he := ConcreteCategory.congr_hom
      (NatTrans.congr_app (constantFunctor_evaluation (C := C) k) (Opposite.op ⦋0⦌)) z
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app (Opposite.op ⦋0⦌)
      ((curry (snd K C)).app (Opposite.op ⦋0⦌) z) = z at he
    rw [he]
    exact hz
  · intro F hF
    apply (functor_pushout_iff_pointwise _).2
    intro k
    rw [Category.assoc, constantFunctor_evaluation, Category.comp_id]
    exact hF

/-- 概要：全同値な標準単体図式の包含は零対象と全押し出しを保つ。
方針：零頂点の評価と定数関手の合成との関手同型を使う。
規約：全図式の関手圏への元の包含。使われ方：gapped 条件の輸送。 -/
lemma equivalenceDiagramι_preservesSConstructionData (m : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    PreservesSConstructionData (equivalenceDiagramι (Δ[m] : SSet.{u}) C) := by
  let p := equivalenceDiagramEvaluation (Δ[m] : SSet.{u}) C (stdSimplex.obj₀Equiv.symm 0)
  have hf := (preservesSConstructionData_of_trivialKanFibration p).comp
    (constantFunctor_preservesSConstructionData (Δ[m] : SSet.{u}) C)
  have e := (equivalenceDiagramEvaluation_comparison m C).postcomp
    (equivalenceDiagramι (Δ[m] : SSet.{u}) C)
  rw [Category.assoc, equivalenceDiagramConstant_ι, Category.id_comp] at e
  exact hf.of_functorIso e

/-- 概要：関手圏の Ar 図式が gapped であることは全ての点で判定できる。
方針：対角の零対象と四角形の押し出しをそれぞれ点ごとに判定する。
規約：C は安定な quasicategory。使われ方：二つの添字の交換。 -/
lemma isGapped_functor_iff_pointwise {n : ℕ} {K C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (F : arNerve n ⟶ (ihom K).obj C) :
    IsGapped F ↔ ∀ k : K _⦋0⦌, IsGapped (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) := by
  constructor
  · intro h k
    exact h.postcomp _ (evaluateFunctorAt_preservesSConstructionData k)
  · intro h
    constructor
    · intro i
      exact isZeroVertex_of_pointwise _ (fun k => (h k).1 i)
    · intro i j k l hij hjk hkl
      apply (functor_pushout_iff_pointwise _).2
      intro a
      simpa only [Category.assoc] using (h a).2 i j k l hij hjk hkl

/-- 概要：全同値な標準単体図式の包含は gapped 条件を保ち反映する。
方針：保存は包含の完全性、反映は零頂点での評価の自明ファイブレーションを使う。
規約：元の全同値図式の圏の Ar 図式。使われ方：core S の行への交換。 -/
lemma isGapped_equivalenceDiagramι_iff {n m : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : arNerve n ⟶ equivalenceDiagrams (Δ[m] : SSet.{u}) C) :
    IsGapped F ↔ IsGapped (F ≫ equivalenceDiagramι Δ[m] C) := by
  constructor
  · exact fun h => h.postcomp _ (equivalenceDiagramι_preservesSConstructionData m C)
  · intro h
    apply (isGapped_iff_postcomp_of_trivialKanFibration
      (equivalenceDiagramEvaluation Δ[m] C (stdSimplex.obj₀Equiv.symm 0)) F).2
    exact h.postcomp _
      (evaluateFunctorAt_preservesSConstructionData (stdSimplex.obj₀Equiv.symm 0))

end SerrePositivity.KST.SConstruction
