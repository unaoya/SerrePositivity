module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomComparisonRecovery

/-!
概要：表現可能な相対 Hom の strict 比較の回収を任意のパラメーターへ拡張する。
方針：比較の自然性をパラメーターと相対 Hom の積で課し、恒等射で族を回収する。
規約：全 Hom に厳密に自然な族を扱う。一般の coherent 変換の strictification は別工程。
使われ方：面・退化と両立する比較の回収と、境界付き高次の延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 任意のパラメーターを持ち、全相対 Hom に自然な比較の族。 -/
def RelativeHomComparisonFamily {B : SSet.{u}} (a : Over B)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) (T : SSet.{u}) :=
  {η : ∀ r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B,
      T ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace r.val.hom q.val.hom ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace r.val.hom a.hom //
    ∀ r s,
      (η r ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace s.val.hom r.val.hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a r.val s.val =
      (α_ T (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace r.val.hom q.val.hom)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace s.val.hom r.val.hom)).hom ≫
          (T ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition q.val r.val s.val) ≫ η s}

/-- 一つの相対射の族は、全標的での前合成の比較の族を与える。 -/
def relativeHomComparisonFamilyOfMap {B : SSet.{u}} {a : Over B}
    {q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B} {T : SSet.{u}}
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.hom) : RelativeHomComparisonFamily a q T := by
  refine ⟨fun r ↦ (f ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace r.val.hom q.val.hom) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a q.val r.val, ?_⟩
  intro r s
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨t, g⟩, h⟩
  exact congrArg (fun k ↦ k.app n (f.app n t, g, h))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_assoc a q.val r.val s.val)

/-- 比較の族を表現する対象の恒等射で評価し、相対射の族を回収する。 -/
def relativeHomComparisonFamilyMap {B : SSet.{u}} {a : Over B}
    {q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B} {T : SSet.{u}} (η : RelativeHomComparisonFamily a q T) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.hom :=
  lift (𝟙 T) (toUnit T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity q.val) ≫ η.val q

/-- 比較の族の全成分は、恒等射での評価から相対合成により復元される。 -/
lemma relativeHomComparisonFamilyMap_component {B : SSet.{u}} {a : Over B}
    {q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B} {T : SSet.{u}} (η : RelativeHomComparisonFamily a q T)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    (relativeHomComparisonFamilyOfMap (relativeHomComparisonFamilyMap η)).val r = η.val r := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨t, f⟩
  have h := congrArg (fun k ↦ k.app n
    ((t, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity q.val).app n PUnit.unit), f)) (η.property q r)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a q.val r.val).app n
    ((η.val q).app n (t, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity q.val).app n PUnit.unit), f) =
    (η.val r).app n (t, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition q.val q.val r.val).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity q.val).app n PUnit.unit, f)) at h
  have hi := congrArg (fun k ↦ k.app n f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity_comp q.val r.val)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition q.val q.val r.val).app n
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity q.val).app n PUnit.unit, f) = f at hi
  rw [hi] at h
  exact h

/-- 恒等射での評価の後に全標的の比較を作ると、元の族を回収する。 -/
lemma relativeHomComparisonFamilyOfMap_map {B : SSet.{u}} {a : Over B}
    {q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B} {T : SSet.{u}} (η : RelativeHomComparisonFamily a q T) :
    relativeHomComparisonFamilyOfMap (relativeHomComparisonFamilyMap η) = η := by
  apply Subtype.ext
  funext r
  exact relativeHomComparisonFamilyMap_component η r

/-- 相対射の族から作った比較を恒等射で評価すると、同じ相対射の族を回収する。 -/
lemma relativeHomComparisonFamilyMap_ofMap {B : SSet.{u}} {a : Over B}
    {q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B} {T : SSet.{u}}
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.hom) :
    relativeHomComparisonFamilyMap (relativeHomComparisonFamilyOfMap f) = f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro t
  exact congrArg (fun k ↦ k.app n (f.app n t)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_id a q.val)

/-- 相対射の族と、全 Hom に自然な strict 比較の族は全単射で対応する。 -/
def relativeHomComparisonFamilyEquiv {B : SSet.{u}} (a : Over B)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) (T : SSet.{u}) :
    (T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.hom) ≃ RelativeHomComparisonFamily a q T where
  toFun := relativeHomComparisonFamilyOfMap
  invFun := relativeHomComparisonFamilyMap
  left_inv := relativeHomComparisonFamilyMap_ofMap
  right_inv := relativeHomComparisonFamilyOfMap_map

/-- 比較の族を任意のパラメーター射で厳密に制限する。 -/
def RelativeHomComparisonFamily.restrict {B : SSet.{u}} {a : Over B}
    {q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B} {S T : SSet.{u}} (η : RelativeHomComparisonFamily a q T)
    (k : S ⟶ T) : RelativeHomComparisonFamily a q S := by
  refine ⟨fun r ↦ (k ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace r.val.hom q.val.hom) ≫ η.val r, ?_⟩
  intro r s
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨t, f⟩, g⟩
  exact congrArg (fun h ↦ h.app n ((k.app n t, f), g)) (η.property r s)

/-- パラメーターの恒等射での制限は元の比較の族。 -/
lemma RelativeHomComparisonFamily.restrict_id {B : SSet.{u}} {a : Over B}
    {q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B} {T : SSet.{u}} (η : RelativeHomComparisonFamily a q T) :
    η.restrict (𝟙 T) = η := by
  apply Subtype.ext
  funext r
  simp only [RelativeHomComparisonFamily.restrict, id_whiskerRight, Category.id_comp]

/-- パラメーターの二回の制限は合成射への制限そのもの。 -/
lemma RelativeHomComparisonFamily.restrict_comp {B : SSet.{u}} {a : Over B}
    {q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B} {R S T : SSet.{u}} (η : RelativeHomComparisonFamily a q T)
    (k : S ⟶ T) (l : R ⟶ S) :
    (η.restrict k).restrict l = η.restrict (l ≫ k) := by
  apply Subtype.ext
  funext r
  simp only [RelativeHomComparisonFamily.restrict, comp_whiskerRight, Category.assoc]

/-- 恒等射での回収はパラメーターの制限と厳密に可換。 -/
lemma relativeHomComparisonFamilyMap_restrict {B : SSet.{u}} {a : Over B}
    {q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B} {S T : SSet.{u}}
    (η : RelativeHomComparisonFamily a q T) (k : S ⟶ T) :
    relativeHomComparisonFamilyMap (η.restrict k) = k ≫ relativeHomComparisonFamilyMap η := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro t
  rfl

/-- 前合成の比較の族の構成もパラメーター制限と厳密に可換。 -/
lemma relativeHomComparisonFamilyOfMap_restrict {B : SSet.{u}} {a : Over B}
    {q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B} {S T : SSet.{u}}
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.hom) (k : S ⟶ T) :
    (relativeHomComparisonFamilyOfMap f).restrict k = relativeHomComparisonFamilyOfMap (k ≫ f) := by
  apply Subtype.ext
  funext r
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨t, g⟩
  rfl

/-- 既存の豊穣比較をテンソル単位をパラメーターとする比較の族にする。 -/
def relativeHomComparisonFamilyOfComparison {B : SSet.{u}} {a : Over B}
    {q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation q.val)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation a)) : RelativeHomComparisonFamily a q (𝟙_ SSet.{u}) := by
  refine ⟨fun r ↦ (λ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace r.val.hom q.val.hom)).hom ≫ η.val r, ?_⟩
  intro r s
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨t, f⟩, g⟩
  cases t
  exact congrArg (fun k ↦ k.app n (f, g)) (η.property r s)

/-- 単位をパラメーターとする族からの回収は、既存の恒等射での回収と一致する。 -/
lemma relativeHomComparisonFamilyMap_ofComparison {B : SSet.{u}} {a : Over B}
    {q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation q.val)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation a)) :
    relativeHomComparisonFamilyMap (relativeHomComparisonFamilyOfComparison η) =
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonUnit η := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro t
  cases t
  rfl

/-- 任意のホーン上の strict 比較の族は、指定したホーンを保って延長できる。 -/
lemma exists_relativeHomComparisonFamily_horn_extension {B : SSet.{u}} (a : Over B)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) {n : ℕ} (i : Fin (n + 2))
    (η : RelativeHomComparisonFamily a q (horn (n + 1) i)) :
    ∃ θ : RelativeHomComparisonFamily a q Δ[n + 1], θ.restrict (horn (n + 1) i).ι = η := by
  obtain ⟨f, hf⟩ := KanComplex.hornFilling (relativeHomComparisonFamilyMap η)
  refine ⟨relativeHomComparisonFamilyOfMap f, ?_⟩
  rw [relativeHomComparisonFamilyOfMap_restrict, ← hf, relativeHomComparisonFamilyOfMap_map]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
