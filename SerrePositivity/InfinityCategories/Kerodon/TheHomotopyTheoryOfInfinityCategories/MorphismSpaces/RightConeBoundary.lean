module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SectionsFiberwiseComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne

/-!
概要：右ファイブレーションによる点上の slice の後合成は自明 Kan fibration。
方針：境界と右の一点の join を最後のホーンに同定し、slice の普遍性で充填を移す。
規約：元の全空間と底の quasicategory 性は要求しない。
使われ方：Kerodon 4.3.7.8（Tag 0196） の双対、7.4.1.6、7.5.4.6 の錐の写像空間の比較 span。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：境界と右の一点の join は標準単体の最後のホーンの逆像。
方針：連結写像の欠落頂点の表示で、右の唯一の頂点を除いた欠落を左因子に移す。
規約：n=0 も含む。
使われ方：Kerodon 4.3.7.8（Tag 0196） の双対の right anodyne 性の生成セル。 -/
lemma rightConeBoundary_horn_preimage (n : ℕ) :
    (horn (n + 0 + 1) (Fin.last (n + 1))).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} n 0).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft (boundary n) (Δ[0] : SSet.{u}) := by
  ext ⟨⟨d⟩⟩ s
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom.app (Opposite.op ⦋d⦌) s ∈
    (horn (n + 0 + 1)
      (Fin.cast (by omega) (Fin.last (n + 1) : Fin ((n + 1) + (0 + 1))))).obj _) ↔ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_horn_joinStdSimplexIso_iff n 0 d s (Fin.last (n + 1)),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_joinSubcomplexLeft,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem_boundary_iff, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.missing_concat_iff]
  constructor
  · rintro (⟨v, _, hm⟩ | ⟨v, hv, _⟩)
    · exact ⟨v, hm⟩
    · have he : v.natAdd (n + 1) = Fin.last (n + 1) := by
        have : v = 0 := Fin.ext (by have := v.isLt; omega)
        rw [this]
        rfl
      exact (hv he).elim
  · rintro ⟨v, hm⟩
    refine Or.inl ⟨v, ?_, hm⟩
    intro he
    have hv := congrArg Fin.val he
    change v.val = n + 1 at hv
    have := v.isLt
    omega

/-- 概要：境界と右の一点の join の包含は right anodyne。
方針：標準単体の同型で最後のホーン包含へ移す。
規約：最後のホーンは right horn に含まれる。
使われ方：Kerodon 4.3.7.8（Tag 0196） の双対の slice の後合成の境界充填。 -/
lemma joinBoundary_point_rightAnodyne (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (boundary n).ι (𝟙 (Δ[0] : SSet.{u}))) := by
  have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (horn.{u} (n + 0 + 1) (Fin.last (n + 1))).ι :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions_horn (Fin.last (n + 1)) (by change 0 < n + 1; omega)
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft (boundary n) (Δ[0] : SSet.{u})).ι := by
    rw [← rightConeBoundary_horn_preimage]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.arrow_mk_iso_iff
      (Arrow.isoMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso (horn (n + 0 + 1) (Fin.last (n + 1)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0) (by rfl))).mpr hh
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.comp_mem
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeftIso (boundary n) (Δ[0] : SSet.{u})).hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft (boundary n) (Δ[0] : SSet.{u})).ι
    (MorphismProperty.of_isIso _ _) hr
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeftIso_hom_ι] using he

/-- 概要：右ファイブレーションの点上の slice の後合成は全境界を持ち上げる。
方針：slice の curry の四角形を境界と右の一点の join の四角形へ移す。
規約：固定図式の始域は標準零単体。
使われ方：Kerodon 4.3.7.8（Tag 0196） の双対、7.4.1.6 の写像空間の比較 span。 -/
lemma sliceOverPostcomp_boundary_lifting_of_rightFibration {E B : SSet.{u}}
    (c : (Δ[0] : SSet.{u}) ⟶ E) (r : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r] (n : ℕ) :
    HasLiftingProperty (boundary n).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp c r) := by
  constructor
  intro a b sq
  have hT : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (boundary n).ι (𝟙 (Δ[0] : SSet.{u}))) r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b) := by
    constructor
    have he := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry sq.w
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp] at he
    exact he
  have := joinBoundary_point_rightAnodyne n r _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem
  let L := hT.lift
  have hfixed : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0] ≫ L = c := by
    have he := congrArg
      (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (boundary n : SSet.{u}) (Δ[0] : SSet.{u}) ≫ z) hT.fac_left
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp] at he
    exact he.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective c
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry]
    exact hT.fac_left
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective (c ≫ r)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry]
    exact hT.fac_right

/-- 概要：右ファイブレーションの点上の slice の後合成は自明 Kan fibration。
方針：全境界の持ち上げ性で判定する。
規約：E と B の quasicategory 性は不要。
使われ方：Kerodon 4.3.7.8（Tag 0196） の双対、7.5.4.6 の比較射の始域への自明な射影。 -/
lemma sliceOverPostcomp_trivialKanFibration_of_rightFibration {E B : SSet.{u}}
    (c : (Δ[0] : SSet.{u}) ⟶ E) (r : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp c r) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
    (sliceOverPostcomp_boundary_lifting_of_rightFibration c r)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.4.3.1" (partial := special) "仮定：Cartesian ファイブレーション p と図式（Lean が強い：p が右ファイブレーションで、図式を一点に限る）。結論：スライス間の後合成が自明 Kan ファイブレーション（Lean が弱い：一般の図式と、スライスの辺の Cartesian 性を像で判定する同値はない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceOverPostcomp_trivialKanFibration_of_rightFibration
