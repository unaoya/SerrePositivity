module
public import SerrePositivity.InfinityCategories.Derived.ComplexTrianglePostcomposition
public import SerrePositivity.InfinityCategories.Derived.FiberCofiberDescEquivalence

/-! # 双対比較の後合成三角形

概要：cofiber 三角形を明示的比較で後合成すると、元の標準 fiber 三角形になる。
方針：二脚・対角・ホモトピーの厳密な保存を二単体の外延性へ渡す。
規約：実際の二単体の等式。使われ方：D7 の比較三単体の終点面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
variable {S : Type u} [CommRing S] {B C D : Complex S}

/-- 下側の標準 cofiber 三角形の後合成は元の fiber 下三角形。 -/
lemma fiberCofiberLower_postcompose (g : B ⟶ D) (h : C ⟶ D) :
    postcomposeComplexTriangle (pullbackProjectionB g h)
      (pushoutInclusionB (pullbackProjectionB g h) (pullbackProjectionC g h))
      (pushoutDiagonal (pullbackProjectionB g h) (pullbackProjectionC g h))
      (mappingCone.inl (cofiberDifference (pullbackProjectionB g h) (pullbackProjectionC g h)))
      (pushoutHomotopy_differential _ _) (fiberCofiberDesc g h) =
        (fiberLowerTriangle g h).simplex := by
  apply dgSimplex2_ext
  · funext i; fin_cases i <;> rfl
  · rfl
  · apply heq_of_eq
    exact congrArg Cochain.ofHom (fiberCofiberDesc_inclusionB g h)
  · apply heq_of_eq
    exact congrArg Cochain.ofHom (fiberCofiberDesc_diagonal g h)
  · exact heq_of_eq (fiberCofiberDesc_homotopy g h)

/-- 上側の標準 cofiber 三角形の後合成は元の fiber 上三角形。 -/
lemma fiberCofiberUpper_postcompose (g : B ⟶ D) (h : C ⟶ D) :
    postcomposeComplexTriangle (pullbackProjectionC g h)
      (pushoutInclusionC (pullbackProjectionB g h) (pullbackProjectionC g h))
      (pushoutDiagonal (pullbackProjectionB g h) (pullbackProjectionC g h)) 0
      (by simp only [δ_zero, pushoutDiagonal, sub_self]) (fiberCofiberDesc g h) =
        (fiberUpperTriangle g h).simplex := by
  apply dgSimplex2_ext
  · funext i; fin_cases i <;> rfl
  · rfl
  · apply heq_of_eq
    exact congrArg Cochain.ofHom (fiberCofiberDesc_inclusionC g h)
  · apply heq_of_eq
    exact congrArg Cochain.ofHom (fiberCofiberDesc_diagonal g h)
  · exact heq_of_eq (Cochain.zero_comp _ (add_zero (-1)))

end SerrePositivity.InfinityCategories
