module
public import SerrePositivity.InfinityCategories.Derived.DGModulePropertyChoices
public import SerrePositivity.InfinityCategories.Derived.DGModulePropertyStability
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorChoice

/-! # 三角的対象条件を満たす dg 加群の包含の完全性

概要：K(D) の三角的対象条件による充満部分圏の native 包含は完全。
方針：各実辺で標準 cone 四角形を選び、その包含像が元の四角形であることを使う。
規約：任意の cofiber 列の保存を結論する。使われ方：前三角 dg 圏の Yoneda 埋め込み。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : ObjectProperty (ModuleHomotopyCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- 各部分圏内の実辺には、周囲でも押し出しとなる cofiber 四角形がある。 -/
lemma dgModuleProperty_cofiber_exists_preserved
    {x y : (dgModulePropertyNerve A D P) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (dgModulePropertyNerve A D P)) x y) :
    ∃ s : CofiberSquare e, IsPushoutSquare
      (s.square ≫ dgNerve.map (dgFullSubcategoryInclusion A (RightModule A D)
        (dgModuleHomotopyProperty A D P))) := by
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  let a := dgModulePropertyAmbientEdge A D P e
  let f := edgeClosed a
  let L := dgModulePropertyConeSquare A D P f M.property N.property
  have he : (dgModuleEdge A D f).edge = a.edge :=
    congrArg Truncated.Edge.edge (dgModuleEdge_edgeClosed A D a)
  let s : CofiberSquare e := {
    square := L
    zero_corner := dgFullSquareLift_zero_corner A _ _ _ _
      (dgModuleConeZeroTriangle A D f).zero_corner
    bottom_edge := by
      apply dgFullSquareLift_edge A (RightModule A D)
        (dgModuleHomotopyProperty A D P) _ _ _ e
      rw [dgModuleConeSquare_bottom]
      exact congrArg SSet.yonedaEquiv.symm he
    isPushout := dgModulePropertyConeSquare_isPushout A D P f M.property N.property }
  refine ⟨s, ?_⟩
  change IsPushoutSquare (dgModulePropertyConeSquare A D P f M.property N.property ≫ _)
  dsimp only [dgModulePropertyConeSquare]
  rw [dgFullSquareLift_inclusion]
  exact dgModuleConeSquare_isPushout A D f

/-- 三角的条件で閉じた全 dg 加群の充満部分圏の包含は完全。 -/
theorem dgModulePropertyInclusion_isExactFunctor :
    IsExactFunctor (dgNerve.map (dgFullSubcategoryInclusion A (RightModule A D)
      (dgModuleHomotopyProperty A D P))) :=
  isExactFunctor_of_preserves_chosen_cofibers _
    (dgFunctorNerve_preservesZeroVertices _) (dgModuleProperty_cofiber_exists_preserved A D P)

/-- 前三角 dg 圏のホモトピー表現可能部分から全加群への実包含は完全。 -/
theorem dgRepleteRepresentablesInclusion_isExactFunctor [IsDGPretriangulated A D] :
    IsExactFunctor (dgNerve.map (dgFullSubcategoryInclusion A (RightModule A D)
      (dgHomotopyRepresentable A D))) :=
  dgModulePropertyInclusion_isExactFunctor A D (dgRepresentableHomotopyProperty A D)

end SerrePositivity.InfinityCategories
