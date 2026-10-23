module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeTransformationMonomorphism
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeTransformationFatComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.JoinRightRelativeExtension

/-!
概要：native な余錐から定値変換空間への標準比較は厳密な左逆を持つ。
方針：比較の像を部分パラメータとして固定し、fat join の恒等族を相対的に延長する。
規約：左逆の存在と同値性を区別する。右逆のホモトピーは別途必要。
使われ方：全空間模型の余極限の普遍性の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の native な余錐の全族を厳密に保つ、比較射の左逆が存在する。
方針：単射な比較を右側の部分族として固定し、全変換を join の余錐へ回収する。
規約：標的 X の quasicategory 性だけを要求。使われ方：比較同値の単位の構成。 -/
lemma coconeTransformationMap_exists_retraction {K X : SSet.{u}} [Quasicategory X]
    (f : K ⟶ X) (z : X _⦋0⦌) :
    ∃ r : intervalMappingSpace (functorVertex f) (functorVertex (SSet.const z)) ⟶
        coconeMappingSpace f z, coconeTransformationMap f z ≫ r = 𝟙 _ := by
  let S := coconeMappingSpace f z
  let T := intervalMappingSpace (functorVertex f) (functorVertex (SSet.const z))
  let c := coconeTransformationMap f z
  let F := constantTransformationFatDiagram (𝟙 T)
  let G : join K S ⟶ X := sliceUnderUncurry (vertexFiberι (sliceUnderProjection f) z)
  have hFG : fatJoinMap (𝟙 K) c ≫ F = fatJoinComparison K S ≫ G := by
    dsimp only [F]
    rw [constantTransformationFatDiagram_precomp, Category.comp_id]
    simpa only [G, Category.id_comp] using coconeTransformationFatDiagram_comparison (𝟙 S)
  obtain ⟨H, hH, hl, hr⟩ := exists_joinDiagram_right_relative_extension c F G hFG
  have hLf : joinInl K T ≫ H = f := hl.trans (constantTransformationFatDiagram_inl (𝟙 T))
  have hRz : joinInr K T ≫ H = SSet.const z :=
    hr.trans (constantTransformationFatDiagram_inr (𝟙 T))
  let r : T ⟶ S := vertexFiberLift (sliceUnderProjection f) z (sliceUnderCurry H hLf)
    (by rw [sliceUnderCurry_projection]; exact hRz)
  refine ⟨r, ?_⟩
  apply vertexFiber_hom_ext (sliceUnderProjection f) z
  rw [Category.assoc, vertexFiberLift_ι, Category.id_comp]
  apply sliceUnderUncurry_injective f
  rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
  exact hH

end SerrePositivity.InfinityCategories.F2
