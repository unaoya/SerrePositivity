module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedFatConeCurry
public import SerrePositivity.InfinityCategories.F1.JoinDiagramRelativeExtension

/-!
概要：slice の頂点 fiber から両端固定の fat join の錐への比較と厳密な左逆。
方針：太い slice の比較の単射性を使い、部分族と両端を保つ相対 join 延長を適用する。
規約：比較射は既存の頂点 fiber と内部 Hom の比較の合成そのもの。
使われ方：Kerodon §4.6.6、7.4.1.6、7.5.4.6 の固定頂点を保つ模型の同値性の準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：slice から太い slice への既存の比較は単射。
方針：uncurry の単射性と fat join 比較のエピ性で任意の二つの族を消去する。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.6.6 の相対 join 延長で既存の部分族を固定する条件。 -/
instance sliceLaxMap_mono {K X : SSet.{u}} (p : K ⟶ X) : Mono (sliceLaxMap p) := by
  constructor
  intro A f g h
  apply sliceOverUncurry_injective
  apply (cancel_epi (fatJoinComparison A K)).mp
  rw [← laxSliceUncurry_comp_sliceLaxMap, ← laxSliceUncurry_comp_sliceLaxMap, h]

/-- 概要：slice の頂点 fiber から両端固定の fat join の錐への標準比較。
方針：内部 Hom の固定頂点の錐への比較と両端固定の fat join 比較を合成する。
規約：元の二つの射を選び直さない。
使われ方：Kerodon 4.6.6.8、7.4.1.6 の実際の比較射の逆の構成。 -/
noncomputable def fixedSliceFatConeComparison {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) : vertexFiber (sliceOverProjection p) x ⟶ fixedEndpointFatConeSpace p x :=
  coneVertexFiberFamilyMap p x ≫ fixedApexFatConeComparison p x

/-- 概要：固定頂点の比較から頂点の条件を忘れると、太い slice の標準比較に一致する。
方針：内部 Hom を経由した比較と太い slice 比較の既存の合成則を使う。
規約：射の厳密な等式であり充填性は不要。
使われ方：Kerodon 4.6.6.8 の比較の単射性と任意パラメータでの展開。 -/
lemma fixedSliceFatConeComparison_toLaxSlice {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) :
    fixedSliceFatConeComparison p x ≫ fixedFatConeToLaxSlice p x =
      vertexFiberι (sliceOverProjection p) x ≫ sliceLaxMap p := by
  change (vertexFiberι (sliceOverProjection p) x ≫ sliceConeFamilyMap p) ≫
    coneFamilyLaxSliceMap p = _
  rw [Category.assoc, sliceConeFamilyMap_comp_coneFamilyLaxSliceMap]

/-- 概要：固定頂点の slice からの標準比較は単射。
方針：太い slice への合成が二つの単射の合成であることから従う。
規約：元の X の充填性を要求しない。
使われ方：Kerodon §4.6.6 の部分族を保つ相対 join 延長の仮定。 -/
instance fixedSliceFatConeComparison_mono {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    Mono (fixedSliceFatConeComparison p x) := by
  have : Mono (fixedSliceFatConeComparison p x ≫ fixedFatConeToLaxSlice p x) := by
    rw [fixedSliceFatConeComparison_toLaxSlice]
    infer_instance
  exact mono_of_mono (fixedSliceFatConeComparison p x) (fixedFatConeToLaxSlice p x)

/-- 概要：固定頂点の slice の族の比較を展開すると、元の錐に fat join 比較を前合成した図式。
方針：太い slice への合成の同定と既存の uncurry の比較を使う。
規約：全てのパラメータ A と実際の族 f について成り立つ。
使われ方：Kerodon §4.6.6 の相対 join 延長の部分族上の一致条件。 -/
lemma fixedSliceFatConeComparison_uncurry {A K X : SSet.{u}} {p : K ⟶ X}
    (x : X _⦋0⦌) (f : A ⟶ vertexFiber (sliceOverProjection p) x) :
    fixedFatConeUncurry (f ≫ fixedSliceFatConeComparison p x) =
      fatJoinComparison A K ≫ sliceOverUncurry (f ≫ vertexFiberι (sliceOverProjection p) x) := by
  rw [fixedFatConeUncurry, Category.assoc, fixedSliceFatConeComparison_toLaxSlice,
    ← Category.assoc, laxSliceUncurry_comp_sliceLaxMap]

/-- 概要：固定頂点の slice から両端固定の fat join の錐への標準比較は厳密な左逆を持つ。
方針：比較の像を部分族として相対 join 延長を行い、頂点と図式を保って slice へ curry する。
規約：K は任意、X の quasicategory 性だけを仮定する。
使われ方：Kerodon §4.6.6、7.4.1.6 の比較の圏同値性の単位の構成。 -/
lemma fixedSliceFatConeComparison_exists_retraction {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) :
    ∃ r : fixedEndpointFatConeSpace p x ⟶ vertexFiber (sliceOverProjection p) x,
      fixedSliceFatConeComparison p x ≫ r = 𝟙 _ := by
  let S := vertexFiber (sliceOverProjection p) x
  let B := fixedEndpointFatConeSpace p x
  let c := fixedSliceFatConeComparison p x
  let F := fixedFatConeUncurry (𝟙 B)
  let G := sliceOverUncurry (vertexFiberι (sliceOverProjection p) x)
  have hFG : fatJoinMap c (𝟙 K) ≫ F = fatJoinComparison S K ≫ G := by
    rw [← fixedFatConeUncurry_precomp, Category.comp_id]
    simpa only [Category.id_comp] using fixedSliceFatConeComparison_uncurry x (𝟙 S)
  obtain ⟨H, hH, hx, hp⟩ := exists_joinDiagram_relative_extension c F G hFG
  have hx' : joinInl B K ≫ H = SSet.const x :=
    hx.trans (fixedFatConeUncurry_inl (𝟙 B))
  have hp' : joinInr B K ≫ H = p := hp.trans (fixedFatConeUncurry_inr (𝟙 B))
  let g := sliceOverCurry H hp'
  have hg : g ≫ sliceOverProjection p = SSet.const x := by
    rw [sliceOverCurry_projection]
    exact hx'
  refine ⟨vertexFiberLift (sliceOverProjection p) x g hg, ?_⟩
  apply vertexFiber_hom_ext (sliceOverProjection p) x
  rw [Category.assoc, vertexFiberLift_ι, Category.id_comp]
  apply sliceOverUncurry_injective
  rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
  exact hH

end SerrePositivity.InfinityCategories.HomotopyLimits
