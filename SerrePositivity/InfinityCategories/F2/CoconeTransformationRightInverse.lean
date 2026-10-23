module

public import SerrePositivity.InfinityCategories.F2.CoconeTransformationFatComparison
public import SerrePositivity.InfinityCategories.F2.ConstantTransformationFatHomotopy
public import SerrePositivity.InfinityCategories.F1.Joins.JoinEndpointLifting
public import SerrePositivity.InfinityCategories.F1.Joins.JoinEndpointMaps

/-!
概要：native な余錐から定値変換空間への標準比較はホモトピー右逆を持つ。
方針：任意の変換の族の fat join 図式を両端固定で回収し、比較ホモトピーを curry する。
規約：元の図式と指定頂点をホモトピーの全時間で保持する。
使われ方：標準比較の同値性から一般 coherent な余錐の普遍性へ進む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：定値頂点への変換の任意の族は native な余錐の像にホモトピック。
方針：両端固定の join 図式を回収し、全ホモトピーを変換空間へ戻す。
規約：パラメータの小ささ・有限性は不要。使われ方：比較のホモトピー右逆。 -/
lemma coconeTransformationMap_exists_homotopy {K X T : SSet.{u}} [Quasicategory X]
    {f : K ⟶ X} {z : X _⦋0⦌}
    (a : T ⟶ intervalMappingSpace (functorVertex f) (functorVertex (SSet.const z))) :
    ∃ b : T ⟶ coconeMappingSpace f z,
      Nonempty (SSet.Homotopy (b ≫ coconeTransformationMap f z) a) := by
  let F := constantTransformationFatDiagram a
  obtain ⟨G, hG, H, hH, _⟩ := exists_joinDiagram_of_fatJoinDiagram
    (fatJoinEndpointInclusion K T ≫ F) F rfl
  have hLf : joinInl K T ≫ G = f := by
    have h := congrArg (fun q ↦ joinEndpointInl K T ≫ q) hG
    simpa only [← Category.assoc, joinEndpointInl_inclusion, joinEndpointInl_fatInclusion,
      F, constantTransformationFatDiagram_inl] using h
  have hRz : joinInr K T ≫ G = SSet.const z := by
    have h := congrArg (fun q ↦ joinEndpointInr K T ≫ q) hG
    simpa only [← Category.assoc, joinEndpointInr_inclusion, joinEndpointInr_fatInclusion,
      F, constantTransformationFatDiagram_inr] using h
  let b : T ⟶ coconeMappingSpace f z :=
    vertexFiberLift (sliceUnderProjection f) z (sliceUnderCurry G hLf)
      (by rw [sliceUnderCurry_projection]; exact hRz)
  have hb : sliceUnderUncurry (b ≫ vertexFiberι (sliceUnderProjection f) z) = G := by
    rw [vertexFiberLift_ι, sliceUnderUncurry_curry]
  have hFb : constantTransformationFatDiagram (b ≫ coconeTransformationMap f z) =
      fatJoinComparison K T ≫ G := by
    rw [coconeTransformationFatDiagram_comparison, hb]
  have hfH : (fatJoinInl K T ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ f := by
    have hh := congrArg (fun q ↦ (joinEndpointInl K T ▷ (Δ[1] : SSet.{u})) ≫ q) hH
    change (fatJoinInl K T ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst K Δ[1] ≫ fatJoinInl K T ≫ F at hh
    rw [constantTransformationFatDiagram_inl] at hh
    exact hh
  have hzH : (fatJoinInr K T ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const z := by
    have hh := congrArg (fun q ↦ (joinEndpointInr K T ▷ (Δ[1] : SSet.{u})) ≫ q) hH
    change (fatJoinInr K T ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst T Δ[1] ≫ fatJoinInr K T ≫ F at hh
    rw [constantTransformationFatDiagram_inr, SSet.comp_const] at hh
    exact hh
  let H' : SSet.Homotopy (constantTransformationFatDiagram (b ≫ coconeTransformationMap f z))
      (constantTransformationFatDiagram a) :=
    ⟨H.h, H.h₀.trans hFb.symm, H.h₁, by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property⟩
  exact ⟨b, ⟨constantTransformationHomotopyOfFatDiagram _ _ H' hfH hzH⟩⟩

end SerrePositivity.InfinityCategories.F2
