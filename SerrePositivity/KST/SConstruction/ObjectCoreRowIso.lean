module
public import SerrePositivity.KST.SConstruction.CoreGappedEquivalenceDiagram

/-! # object S の行と core S の交換した行の同型
概要：D(m,w) の object S は、core S の m 単体を行に持つ単体集合と同型。
方針：二つの包含の単射性で Ar の制限との自然性を確認し、Yoneda 同値で束ねる。
規約：行の単体作用素に厳密に自然。使われ方：Fiore–Pieper Proposition 4.27。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：gapped 全同値図式の交換は Ar の添字制限と可換。
方針：包含を通して内部 Hom の交換の自然性に帰着する。
規約：任意の単調写像を含む。使われ方：行の同型の単体的自然性。 -/
lemma gappedEquivalenceDiagramCoreMap_sMap {l n m : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (θ : Fin (l + 1) →o Fin (n + 1))
    (v : (sConstruction n (equivalenceDiagrams (Δ[m] : SSet.{u}) C)) _⦋0⦌) :
    gappedEquivalenceDiagramCoreMap
        ((sMap (equivalenceDiagrams (Δ[m] : SSet.{u}) C) θ).app (Opposite.op ⦋0⦌) v) =
      gappedEquivalenceDiagramCoreMap v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sMap C θ) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction l C)).ι).1
  apply (cancel_mono (gappedSubcomplex l C).ι).1
  rw [Category.assoc, gappedEquivalenceDiagramCoreMap_ι]
  rw [Category.assoc (gappedEquivalenceDiagramCoreMap v)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sMap C θ)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι]
  simp only [Category.assoc]
  rw [sMap_ι]
  rw [← Category.assoc, ← Category.assoc,
    Category.assoc (gappedEquivalenceDiagramCoreMap v)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C)).ι (gappedSubcomplex n C).ι,
    gappedEquivalenceDiagramCoreMap_ι]
  rw [gappedDiagram_sMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre]

/-- 概要：D(m,w) の object S と core S の m 単体からなる行は単体集合として同型。
方針：gapped 図式の交換の同値と Yoneda 同値を各次数で合わせる。
規約：全 gapped 図式と全ての高次単体を保持する。使われ方：object/core 実現の行の比較。 -/
def objectCoreRowIso (m : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    objectSConstruction (equivalenceDiagrams (Δ[m] : SSet.{u}) C) ≅
      simplicialCoreSConstruction C ⋙
        (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋m⦌) :=
  NatIso.ofComponents (fun n => Equiv.toIso
    ((gappedEquivalenceDiagramVerticesEquiv n.unop.len m C).trans SSet.yonedaEquiv)) (by
      intro n l θ
      apply ConcreteCategory.hom_ext
      intro v
      change SSet.yonedaEquiv (gappedEquivalenceDiagramCoreMap
        ((sMap (equivalenceDiagrams (Δ[m] : SSet.{u}) C) θ.unop.toOrderHom).app
          (Opposite.op ⦋0⦌) v)) = _
      rw [gappedEquivalenceDiagramCoreMap_sMap, SSet.yonedaEquiv_comp]
      rfl)

end SerrePositivity.KST.SConstruction
