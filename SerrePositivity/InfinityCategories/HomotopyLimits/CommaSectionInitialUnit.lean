module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaUnitRepresentative

/-!
概要：coherent な普遍 comma 切断の単位に、始対象条件を戻す。
方針：同じ標的の二重 fiber 内で矢印の Hom 類を比較し、頂点同型で始対象性を移す。
規約：代表の厳密な一致を仮定しない。使われ方：普遍矢印から随伴の構成への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 各成分が comma の始対象である切断から作る単位は、始対象条件を満たす。 -/
lemma commaSectionUnit_initialCondition {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X)
    (s : X ⟶ unitComma G) (hs : s ≫ unitCommaSource G = 𝟙 X)
    (h : ∀ x : X _⦋0⦌, IsInitialVertex (commaSectionFiberVertex G s hs x)) :
    UnitCommaInitialCondition (commaSectionUnit G s hs) := by
  apply (unitCommaInitialCondition_iff _).mpr
  intro x
  let η := commaSectionUnit G s hs
  let v := commaSectionTargetFiberVertex G s hs x
  let w := unitCommaSectionTargetFiberVertex η x
  have hh : Truncated.HomotopyCategory.homMk
      (commaTargetFiberArrow G x ((s ≫ unitCommaTarget G).app (Opposite.op ⦋0⦌) x)
        v).toTruncated = Truncated.HomotopyCategory.homMk
      (commaTargetFiberArrow G x ((s ≫ unitCommaTarget G).app (Opposite.op ⦋0⦌) x)
        w).toTruncated := by
    dsimp only [v]
    rw [commaSectionTargetFiberArrow_eq, ← commaSectionUnit_component]
    exact (unitCommaSectionTargetFiberArrow_hom η x).symm
  exact (unitCommaTargetFiber_isInitial_iff_of_homMk_eq G x _ v w hh).mp (h x)

/-- 相対始対象切断の同じ円柱の単位は、選び直した代表でも comma の普遍矢印。 -/
lemma commaSectionUnit_initialCondition_of_relativeInitial {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X)
    (s : X ⟶ unitComma G) (hs : s ≫ unitCommaSource G = 𝟙 X)
    (h : ∀ x : X _⦋0⦌, InitialBoundaryLifting (unitCommaSource G)
      (s.app (Opposite.op ⦋0⦌) x)) : UnitCommaInitialCondition (commaSectionUnit G s hs) :=
  commaSectionUnit_initialCondition G s hs fun x ↦
    InitialBoundaryLifting.isInitialVertex_fiber (unitCommaSource G) x
      (commaSectionFiberVertex G s hs x) (h x)

/-- 各 comma の始対象から、一つの coherent な関手と始対象条件を持つ単位が存在。 -/
lemma exists_unit_initialCondition_of_fiberInitial {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X)
    (h : ∀ x : X _⦋0⦌, ∃ v : (unitCommaFiber G x) _⦋0⦌, IsInitialVertex v) :
    ∃ (F : X ⟶ Y) (η : FunctorHom (𝟙 X) (F ≫ G)), UnitCommaInitialCondition η := by
  obtain ⟨s, hs, hi⟩ := exists_unitCommaSection_of_fiberInitial G h
  exact ⟨s ≫ unitCommaTarget G, commaSectionUnit G s hs,
    commaSectionUnit_initialCondition_of_relativeInitial G s hs hi⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
