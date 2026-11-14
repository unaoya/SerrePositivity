module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.SemifreeCofiberSuspensionComponents
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonComposition

/-! # 標準 cofiber 列の実際の接続射

概要：安定構造の接続射を、標準 cone から suspension への鎖写像の類と同定する。
方針：始点で恒等な二つの正方形比較は等しいことを用い、構成した比較の終点を読む。
規約：通常の導来圏から接続射を引き戻さない。使われ方：D7 の第三射の像の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- 実際の cofiber 四角形の始点に合わせた標準 suspension。 -/
def semifreeCofiberSuspensionSquare (f : X.val ⟶ Y.val) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).square 0 0) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).changeSource (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_vertex00 f).symm

/-- 構成した図式射は普遍性で選ばれた cofiber 比較射に等しい。 -/
lemma semifreeCofiberSuspensionHom_eq_comparison (f : X.val ⟶ Y.val) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionHom f =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).square
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f) (semifreeCofiberSuspensionSquare f) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparison_hom_ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).square
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f) (semifreeCofiberSuspensionSquare f)
  apply Arrow.mk_injective
  refine (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionHom_source_arrow f).trans ?_
  symm
  exact (congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_source
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).square (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f)
      (semifreeCofiberSuspensionSquare f))).trans
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_map_eqToHom (𝟭 _) (congrArg SSet.HomotopyCategory.mk
      (semifreeCofiberSuspensionSquare f).source_eq.symm))

/-- 標準 cofiber の suspension への接続射は cone 写像の h の類。 -/
lemma semifreeCofiberConnectingToSuspension_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f) (semifreeCofiberSuspensionSquare f)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f))
          (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionHom_target_arrow f
  rw [semifreeCofiberSuspensionHom_eq_comparison, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_target] at h
  exact h

/-- 接続射の端点を標準 cone と標準 suspension の頂点で正規化した式。 -/
lemma semifreeCofiberConnectingToSuspension (f : X.val ⟶ Y.val) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f) (semifreeCofiberSuspensionSquare f) =
      eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_vertex11 f)) ≫
        SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f))
            (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)) ≫
        eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare_vertex X).symm) := by
  obtain ⟨hx, hy, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp
    (semifreeCofiberConnectingToSuspension_arrow f)
  exact hf

end SerrePositivity.InfinityCategories.Project.DerivedCategories
