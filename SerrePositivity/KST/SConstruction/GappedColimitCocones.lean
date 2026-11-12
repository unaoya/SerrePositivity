module
public import SerrePositivity.KST.SConstruction.FullSubcomplexColimits
public import SerrePositivity.KST.SConstruction.GappedPointwiseColimit

/-! # S_n 内の点ごとの普遍余錐
概要：点ごとの余極限が存在する gapped な span は S_n 内でも点ごとの普遍余錐を持つ。
方針：周囲の点ごとの補完の gapped 閉性を使い全部分複体へ戻す。
規約：必要な点ごとの存在を明示する。使われ方：包含の cofiber 保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：点ごとの余極限が存在する S_n の span に、点ごとの普遍余錐を選べる。
方針：周囲で点ごとの余錐を取り、全頂点の gapped 閉性で S_n に持ち上げる。
規約：入力の図式を厳密に保つ。使われ方：包含後の余極限性の保存。 -/
lemma exists_gapped_pointwiseColimitCocone {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (p : (horn 2 0 : SSet.{u}) ⟶ sConstruction n C)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasPointwiseColimits (p ≫ (gappedSubcomplex n C).ι)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseColimitCone (mapJoinCocone (gappedSubcomplex n C).ι c) := by
  let ι := (gappedSubcomplex n C).ι
  obtain ⟨d, hd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_pointwiseColimitCone (p ≫ ι) hp
  have hg (a : (horn 2 0 : SSet.{u}) _⦋0⦌) : IsGapped
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (horn 2 0 : SSet.{u}) Δ[0] ≫ d.val).app (Opposite.op ⦋0⦌) a)) := by
    rw [d.property]
    exact gappedDiagram_isGapped (p.app (Opposite.op ⦋0⦌) a)
  let d₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (horn 2 0 : SSet.{u}) Δ[0] ≫ d.val) := ⟨d.val, rfl⟩
  have hd' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseColimitCone d₀ := by
    intro a
    exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCocone d₀ a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCocone d a) rfl).2 (hd a)
  have hgd := gapped_pointwiseColimit d.val hd' hg
  let D : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (horn 2 0 : SSet.{u}) Δ[0] ⟶ sConstruction n C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ d.val hgd
  have hD : D ≫ ι = d.val := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  have hDp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (horn 2 0 : SSet.{u}) Δ[0] ≫ D = p := by
    apply (cancel_mono ι).1
    rw [Category.assoc, hD, d.property]
  let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p := ⟨D, hDp⟩
  refine ⟨c, ?_⟩
  have he : mapJoinCocone ι c = d := Subtype.ext hD
  rw [he]
  exact hd

/-- 概要：S_n の点ごとの普遍余錐は S_n 内でも普遍。
方針：周囲の普遍性を全部分複体へ反映する。
規約：C は quasicategory。使われ方：普遍余錐の比較の一方。 -/
lemma isColimitCone_gapped_of_pointwise {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    {p : (horn 2 0 : SSet.{u}) ⟶ sConstruction n C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseColimitCone (mapJoinCocone (gappedSubcomplex n C).ι c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c :=
  isColimitCone_fullSubcomplex_of_ambient (X := (ihom (arNerve n)).obj C) _ c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_pointwise _ hc)

/-- 概要：点ごとの存在があれば S_n の任意の普遍余錐は包含後も点ごとに普遍。
方針：既に構成した点ごとの普遍余錐と S_n 内で同型に比較し包含で写す。
規約：存在前提を省略しない。使われ方：S_n の cofiber の評価。 -/
lemma isPointwiseColimitCone_gappedInclusion_of_hasPointwiseColimits {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] {p : (horn 2 0 : SSet.{u}) ⟶ sConstruction n C}
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasPointwiseColimits (p ≫ (gappedSubcomplex n C).ι))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseColimitCone (mapJoinCocone (gappedSubcomplex n C).ι c) := by
  obtain ⟨d, hd⟩ := exists_gapped_pointwiseColimitCocone p hp
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso d c (isColimitCone_gapped_of_pointwise d hd) hc
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseColimitCone.of_vertexIso hd
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p (gappedSubcomplex n C).ι))

/-- 概要：点ごとの存在があれば S_n の span の余極限性は包含後の余極限性と同値。
方針：点ごとの普遍性による保存と全部分複体による反映を合わせる。
規約：任意の span に存在を主張しない。使われ方：零脚の場合の無条件の保存と反映。 -/
lemma isColimitCone_gappedInclusion_iff_of_hasPointwiseColimits {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] {p : (horn 2 0 : SSet.{u}) ⟶ sConstruction n C}
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasPointwiseColimits (p ≫ (gappedSubcomplex n C).ι)) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (mapJoinCocone (gappedSubcomplex n C).ι c) :=
  ⟨fun hc => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_pointwise _
      (isPointwiseColimitCone_gappedInclusion_of_hasPointwiseColimits hp c hc),
    fun hc => isColimitCone_fullSubcomplex_of_ambient (X := (ihom (arNerve n)).obj C) _ c hc⟩

end SerrePositivity.KST.SConstruction
