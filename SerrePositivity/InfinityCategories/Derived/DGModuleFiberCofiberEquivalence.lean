module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberCofiberHomotopyBoundary
public import SerrePositivity.InfinityCategories.Derived.DGModuleNerveHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-! # dg 加群の標準 fiber と cofiber の比較辺は同値

概要：降下比較と明示的な逆射、両合成の原始元から実辺の可逆性を得る。
方針：実ホモトピー逆の一般判定を使い、道による h への橋を明示する。
規約：標準包含と零ホモトピーを保持する降下射。使われ方：β3 の安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 逆射の後の降下は零原始元によって N の恒等にホモトピック。 -/
def dgModuleFiberCofiberSectionDescHomotopy (f : M ⟶ N) :
    ModuleHomotopy A D (dgModuleFiberCofiberSection A D f ≫ dgModuleFiberCofiberDesc A D f)
      (𝟙 N) := by
  rw [dgModuleFiberCofiberSection_desc]
  exact ⟨0, by rw [map_zero, sub_self]⟩

/-- 実降下射と実逆射はホモトピー商の同型を作る。 -/
def dgModuleFiberCofiberHomotopyIso (f : M ⟶ N) :
    (moduleToHomotopy A D).obj (moduleCone A D (dgModuleFiberProjection A D f)) ≅
      (moduleToHomotopy A D).obj N :=
  dgModuleHomotopyIsoOfInverse A D (dgModuleFiberCofiberDesc A D f)
    (dgModuleFiberCofiberSection A D f) (dgModuleFiberCofiberDescSectionHomotopy A D f)
    (dgModuleFiberCofiberSectionDescHomotopy A D f)

/-- fiber の cofiber から元の標的への実降下比較辺の類は同型。 -/
lemma dgModuleFiberCofiberDesc_isIso (f : M ⟶ N) :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      (dgModuleEdge A D (dgModuleFiberCofiberDesc A D f)).toTruncated) :=
  dgModuleEdge_isIso_of_inverse A D (dgModuleFiberCofiberDesc A D f)
    (dgModuleFiberCofiberSection A D f) (dgModuleFiberCofiberDescSectionHomotopy A D f)
    (dgModuleFiberCofiberSectionDescHomotopy A D f)

/-- 降下比較の実際の nerve 辺は ∞ 圏の可逆辺である。 -/
lemma dgModuleFiberCofiberDesc_isInvertible (f : M ⟶ N) :
    IsInvertibleEdge (X := dgModuleNerve A D)
      (dgModuleEdge A D (dgModuleFiberCofiberDesc A D f)).toTruncated := by
  have := dgModuleFiberCofiberDesc_isIso A D f
  exact (edgeToPathHomotopyCategory _).map_isIso
    (SSet.Truncated.HomotopyCategory₂.homMk
      (dgModuleEdge A D (dgModuleFiberCofiberDesc A D f)).toTruncated)

end SerrePositivity.InfinityCategories
