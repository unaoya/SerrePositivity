module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedSliceFatComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedFatConeHomotopy
public import SerrePositivity.InfinityCategories.F1.Joins.JoinEndpointLifting
public import SerrePositivity.InfinityCategories.F1.Equivalences.EquivalenceRetraction

/-!
概要：slice の頂点 fiber と内部 Hom の固定頂点の錐の模型の標準比較の同値性。
方針：両端固定の fat join 比較からホモトピー右逆を作り、既存の厳密な左逆と合わせる。
規約：頂点と図式を固定した実際の比較射について証明する。
使われ方：Kerodon 4.6.6.8、7.4.1.6、7.5.4.6 の錐の空間と切断模型の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：固定頂点の fat join の錐の任意の族は slice の族の像としてホモトピーまで回収できる。
方針：両端固定の join 比較から錐と図式のホモトピーを取り、固定頂点で curry する。
規約：パラメータ A は任意、X に quasicategory 性だけを要求する。
使われ方：Kerodon §4.6.6、7.4.1.6 の標準比較のホモトピー右逆の構成。 -/
lemma fixedSliceFatConeComparison_exists_homotopy {A K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} {x : X _⦋0⦌} (a : A ⟶ fixedEndpointFatConeSpace p x) :
    ∃ b : A ⟶ vertexFiber (sliceOverProjection p) x,
      Nonempty (SSet.Homotopy (b ≫ fixedSliceFatConeComparison p x) a) := by
  let F := fixedFatConeUncurry a
  obtain ⟨G, hG, H, hH, _⟩ := exists_joinDiagram_of_fatJoinDiagram
    (fatJoinEndpointInclusion A K ≫ F) F rfl
  have hx : joinInl A K ≫ G = SSet.const x := by
    have h := congrArg (fun z ↦ joinEndpointInl A K ≫ z) hG
    simpa only [← Category.assoc, joinEndpointInl_inclusion,
      joinEndpointInl_fatInclusion, F, fixedFatConeUncurry_inl] using h
  have hp : joinInr A K ≫ G = p := by
    have h := congrArg (fun z ↦ joinEndpointInr A K ≫ z) hG
    simpa only [← Category.assoc, joinEndpointInr_inclusion,
      joinEndpointInr_fatInclusion, F, fixedFatConeUncurry_inr] using h
  let b := vertexFiberLift (sliceOverProjection p) x (sliceOverCurry G hp)
    (by rw [sliceOverCurry_projection]; exact hx)
  have hb : sliceOverUncurry (b ≫ vertexFiberι (sliceOverProjection p) x) = G := by
    rw [vertexFiberLift_ι, sliceOverUncurry_curry]
  have hF : fixedFatConeUncurry (b ≫ fixedSliceFatConeComparison p x) =
      fatJoinComparison A K ≫ G := by
    rw [fixedSliceFatConeComparison_uncurry, hb]
  have hxH : (fatJoinInl A K ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst A Δ[1] ≫ SSet.const x := by
    have hh := congrArg (fun z ↦ (joinEndpointInl A K ▷ (Δ[1] : SSet.{u})) ≫ z) hH
    change (fatJoinInl A K ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst A Δ[1] ≫ fatJoinInl A K ≫ F at hh
    rw [fixedFatConeUncurry_inl] at hh
    exact hh
  have hpH : (fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p := by
    have hh := congrArg (fun z ↦ (joinEndpointInr A K ▷ (Δ[1] : SSet.{u})) ≫ z) hH
    change (fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst K Δ[1] ≫ fatJoinInr A K ≫ F at hh
    rw [fixedFatConeUncurry_inr] at hh
    exact hh
  let H' : SSet.Homotopy (fixedFatConeUncurry (b ≫ fixedSliceFatConeComparison p x))
      (fixedFatConeUncurry a) :=
    { h := H.h
      h₀ := H.h₀.trans hF.symm
      h₁ := H.h₁
      rel := by
        apply SSet.hom_ext
        intro d
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }
  exact ⟨b, ⟨fixedFatConeHomotopyOfDiagram (b ≫ fixedSliceFatConeComparison p x) a H'
    hxH hpH⟩⟩

/-- 概要：固定頂点の slice から両端固定の fat join の錐への標準比較は圏同値。
方針：厳密な左逆と恒等族のホモトピー右逆を、Kan な標的の関手の同型で合わせる。
規約：K は任意で、X の quasicategory 性だけを仮定する。
使われ方：Kerodon §4.6.6、7.4.1.6 の固定頂点を保つ錐の模型の比較。 -/
lemma fixedSliceFatConeComparison_isQCatEquivalence {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : IsQCatEquivalence (fixedSliceFatConeComparison p x) := by
  obtain ⟨r, hr⟩ := fixedSliceFatConeComparison_exists_retraction p x
  obtain ⟨b, ⟨H⟩⟩ := fixedSliceFatConeComparison_exists_homotopy
    (𝟙 (fixedEndpointFatConeSpace p x))
  exact isQCatEquivalence_of_retraction_of_rightInverseIso _ r b hr
    (functorIsoOfSimplicialHomotopy H)

/-- 概要：slice の頂点 fiber と内部 Hom の固定頂点の錐の標準比較は圏同値。
方針：fat join への合成と後段の比較の同値性から二対三則を適用する。
規約：大域的な slice の同値だけでなく、固定頂点の実際の射について証明する。
使われ方：Kerodon 4.6.6.8、7.4.1.6、7.5.4.6 の slice 側から共通模型への比較。 -/
lemma coneVertexFiberFamilyMap_isQCatEquivalence {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : IsQCatEquivalence (coneVertexFiberFamilyMap p x) :=
  (fixedApexFatConeComparison_isQCatEquivalence p x).cancel_right
    (fixedSliceFatConeComparison_isQCatEquivalence p x)

/-- 概要：slice の頂点 fiber と内部 Hom の固定頂点の錐の標準比較はホモトピー同値。
方針：両模型の Kan 性と圏同値性を使う。
規約：図式の添字 K の quasicategory 性や非空性は要求しない。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の表現可能な極限判定の模型の移送。 -/
lemma coneVertexFiberFamilyMap_homotopyEquivalence {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (coneVertexFiberFamilyMap p x) :=
  (coneVertexFiberFamilyMap_isQCatEquivalence p x).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
