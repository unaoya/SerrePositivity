module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativePathBoundary
public import SerrePositivity.InfinityCategories.F1B.Fibrations.EquivalenceLiftingInvertible
public import SerrePositivity.InfinityCategories.F1B.KanExtension.PathReplacementLifting
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFamilyPathParameters

/-!
概要：圏論的同値の右持ち上げと inner fibration・可逆辺の持ち上げの同値。
方針：前合成同値で仮の延長を選び、逆向きの可逆 path を境界固定で持ち上げる。
規約：モデル圏の因子分解や追加公理を使わない。
使われ方：標準 isofibration の条件を相対 Kan 構成の右持ち上げ条件へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：inner fibration で可逆辺を持ち上げられる射は単射な前合成同値を右に持ち上げる。
方針：仮の延長と標的図式を指定部分で定値な可逆 path で結び、終点指定で持ち上げる。
規約：元・標的は quasicategory、可逆辺の持ち上げは終点と像を厳密に保つ。
使われ方：isofibration 上での相対 Kan 拡張の組み立て。 -/
lemma equivalenceLifting_of_innerFibration_of_targetLifting
    {D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) [InnerFibration U] (hU : SerrePositivity.InfinityCategories.F1B.InvertibleTargetLifting U) :
    SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U := by
  intro A B i hm hi
  have : Mono i := hm
  constructor
  intro a b sq
  obtain ⟨v, hv⟩ := pre_surjective_of_essentiallySurjective i
    (hi D).choose.isEssentiallySurjective (functorVertex a)
  obtain ⟨c, rfl⟩ := (functorVertexEquiv B D).surjective v
  have hc : i ≫ c = a := (functorVertexEquiv A D).injective hv
  obtain ⟨P, hPi, hP₀, hP₁⟩ := exists_kanEquivalencePath_extension i hi
    (a ≫ U ≫ equivalencePathRefl E) b (c ≫ U)
    (by simp only [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id]; exact sq.w)
    (by simp only [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id]
        rw [← Category.assoc, hc])
  have := kanRelativeEquivalencePathMapAt_one_trivialKanFibration U hU
  have := TrivialKanFibration.mem (p := relativeEquivalencePathMapAt U 1) i inferInstance
  let t : B ⟶ relativeEquivalencePathTargetAt U 1 := pullback.lift P c hP₁
  let s : CommSq (a ≫ equivalencePathRefl D) i (relativeEquivalencePathMapAt U 1) t := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, relativeEquivalencePathMapAt_fst,
        equivalencePathRefl_map, t, pullback.lift_fst]
      exact hPi.symm
    · simp only [Category.assoc, relativeEquivalencePathMapAt_snd,
        equivalencePathRefl_endpoint, Category.comp_id, t, pullback.lift_snd]
      exact hc.symm
  have hsP : s.lift ≫ equivalencePathMap U = P := by
    rw [← relativeEquivalencePathMapAt_fst U 1, ← Category.assoc, s.fac_right]
    exact pullback.lift_fst _ _ _
  refine CommSq.HasLift.mk' {
    l := s.lift ≫ equivalencePathEndpoint D 0
    fac_left := ?_
    fac_right := ?_ }
  · rw [← Category.assoc, s.fac_left, Category.assoc, equivalencePathRefl_endpoint,
      Category.comp_id]
  · rw [Category.assoc, ← equivalencePathMap_endpoint, ← Category.assoc, hsP, hP₀]

/-- 概要：quasicategory 間では圏論的同値の右持ち上げは isofibration の二条件と同値。
方針：内ホーンと可逆区間への適用、および相対 path による逆向きの構成を合わせる。
規約：可逆辺の持ち上げは終点指定の向きで述べる。
使われ方：標準の inner 性と同型持ち上げを相対 Kan 図式の公開入力に使う。 -/
lemma equivalenceLifting_iff_inner_and_invertibleTargetLifting
    {D E : SSet.{u}} [Quasicategory D] [Quasicategory E] (U : D ⟶ E) :
    SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U ↔ InnerFibration U ∧ SerrePositivity.InfinityCategories.F1B.InvertibleTargetLifting U := by
  constructor
  · intro hU
    exact ⟨hU.innerFibration, SerrePositivity.InfinityCategories.F1B.EquivalenceLifting.invertibleTargetLifting hU⟩
  · rintro ⟨hinner, htarget⟩
    have : InnerFibration U := hinner
    intro A B i hm hi
    exact equivalenceLifting_of_innerFibration_of_targetLifting U htarget i hm hi

end SerrePositivity.InfinityCategories.F1B
