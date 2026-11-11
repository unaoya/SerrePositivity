module
public import SerrePositivity.KST.SConstruction.ObjectCoreRowIso
public import SerrePositivity.KST.SConstruction.ObjectRowInclusion

/-! # 定数図式の交換と object/core の行の比較
概要：定数な全同値図式の object S の像を、元の object/core 比較の各行と照合する。
方針：内部 Hom の交換を二つの包含後で計算する。
規約：比較射の取り替えをしない。使われ方：行の弱同値から元の対角比較を証明する。
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

/-- 概要：定数関手の族を交換すると元の図式の頂点への定値射。
方針：内部 Hom の交換を各単体で計算する。
規約：添字と標的は任意。使われ方：定数包含と行の object 包含の照合。 -/
lemma flipConstantFamily {A K C : SSet.{u}} (F : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A K C (F ≫ curry (snd K C)) =
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) : K ⟶ (ihom A).obj C) := by
  change curry ((β_ A K).hom ≫ uncurry (F ≫ curry (snd K C))) = _
  rw [uncurry_natural_left, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：定数図式の object S の像を交換すると元の gapped 対象への定値射。
方針：二つの包含で比較し、定数族の内部 Hom の交換を使う。
規約：安定な入力の元の定数包含。使われ方：行の比較射の照合。 -/
lemma gappedEquivalenceDiagramCoreMap_constant (n m : ℕ) (X : StableModel.{u})
    (v : (sConstruction n X.carrier) _⦋0⦌) :
    gappedEquivalenceDiagramCoreMap
      ((objectSConstructionFunctor.map (equivalenceDiagramStableConstant m X)).app
        (Opposite.op ⦋n⦌) v) =
      (SSet.const ⟨v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex v⟩ :
        (Δ[m] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n X.carrier) : SSet.{u})) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n X.carrier)).ι).1
  apply (cancel_mono (gappedSubcomplex n X.carrier).ι).1
  rw [Category.assoc, gappedEquivalenceDiagramCoreMap_ι, gappedDiagram_objectSFunctor_map]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (Δ[m] : SSet.{u}) X.carrier
    ((gappedDiagram v ≫ equivalenceDiagramConstant Δ[m] X.carrier) ≫
      equivalenceDiagramι Δ[m] X.carrier) = _
  rw [Category.assoc, equivalenceDiagramConstant_ι, flipConstantFamily]
  simp only [SSet.const_comp]
  congr 1
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X.carrier).apply_symm_apply v.val

/-- 概要：定数包含と行の同型の合成は元の object/core 比較の行の射。
方針：交換した定数族の式を各単体で Yoneda 同値に送る。
規約：対象の取り替えや追加の比較射を導入しない。使われ方：各行の弱同値性。 -/
lemma objectCoreRowIso_constant (m : ℕ) (X : StableModel.{u}) :
    objectSConstructionFunctor.map (equivalenceDiagramStableConstant m X) ≫
      (objectCoreRowIso m X.carrier).hom =
      (objectSCoreVertexIso X.carrier).hom ≫
        objectRowInclusion (simplicialCoreSConstruction X.carrier) (Opposite.op ⦋m⦌) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro v
  change SSet.yonedaEquiv (gappedEquivalenceDiagramCoreMap
    ((objectSConstructionFunctor.map (equivalenceDiagramStableConstant m X)).app n v)) = _
  rw [gappedEquivalenceDiagramCoreMap_constant]
  rfl

end SerrePositivity.KST.SConstruction
