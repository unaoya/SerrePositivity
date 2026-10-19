module
public import SerrePositivity.InfinityCategories.Derived.SemifreeCofiberSuspensionComponents
public import SerrePositivity.InfinityCategories.Stable.CofiberComparisonComposition

/-! # 標準 cofiber 列の実際の接続射

概要：安定構造の接続射を、標準 cone から suspension への鎖写像の類と同定する。
方針：始点で恒等な二つの正方形比較は等しいことを用い、構成した比較の終点を読む。
規約：通常の導来圏から接続射を引き戻さない。使われ方：D7 の第三射の像の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {S : Type u} [CommRing S] {X Y : Semifree S}

/-- 実際の cofiber 四角形の始点に合わせた標準 suspension。 -/
def semifreeCofiberSuspensionSquare (f : X.val ⟶ Y.val) :
    SuspensionSquare (squareVertex (semifreeCofiberZeroTriangle f).square 0 0) :=
  (semifreeSuspensionSquare X).changeSource (semifreeCofiberZeroTriangle_vertex00 f).symm

/-- 構成した図式射は普遍性で選ばれた cofiber 比較射に等しい。 -/
lemma semifreeCofiberSuspensionHom_eq_comparison (f : X.val ⟶ Y.val) :
    semifreeCofiberSuspensionHom f =
      cofiberSuspensionComparisonHom (semifreeCofiberZeroTriangle f).square
        (semifreeCofiberZeroTriangle_isCofiberSequence f) (semifreeCofiberSuspensionSquare f) := by
  apply cofiberSuspensionComparison_hom_ext (semifreeCofiberZeroTriangle f).square
    (semifreeCofiberZeroTriangle_isCofiberSequence f) (semifreeCofiberSuspensionSquare f)
  apply Arrow.mk_injective
  refine (semifreeCofiberSuspensionHom_source_arrow f).trans ?_
  symm
  exact (congrArg Arrow.mk (cofiberSuspensionComparisonHom_source
    (semifreeCofiberZeroTriangle f).square (semifreeCofiberZeroTriangle_isCofiberSequence f)
      (semifreeCofiberSuspensionSquare f))).trans
    (arrowMk_map_eqToHom (𝟭 _) (congrArg SSet.HomotopyCategory.mk
      (semifreeCofiberSuspensionSquare f).source_eq.symm))

/-- 標準 cofiber の suspension への接続射は cone 写像の h の類。 -/
lemma semifreeCofiberConnectingToSuspension_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk (cofiberConnectingToSuspension (semifreeCofiberZeroTriangle f)
      (semifreeCofiberZeroTriangle_isCofiberSequence f) (semifreeCofiberSuspensionSquare f)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (derivedChainMapEdge (x := Simplex.vertex (semifreeCofiberZeroObject f))
          (y := Simplex.vertex (semifreeSuspensionObject X)) (cofiberToSuspensionMap f))) := by
  have h := semifreeCofiberSuspensionHom_target_arrow f
  rw [semifreeCofiberSuspensionHom_eq_comparison, cofiberSuspensionComparisonHom_target] at h
  exact h

/-- 接続射の端点を標準 cone と標準 suspension の頂点で正規化した式。 -/
lemma semifreeCofiberConnectingToSuspension (f : X.val ⟶ Y.val) :
    cofiberConnectingToSuspension (semifreeCofiberZeroTriangle f)
        (semifreeCofiberZeroTriangle_isCofiberSequence f) (semifreeCofiberSuspensionSquare f) =
      eqToHom (congrArg SSet.HomotopyCategory.mk (semifreeCofiberZeroTriangle_vertex11 f)) ≫
        SSet.Truncated.HomotopyCategory.homMk
          (derivedChainMapEdge (x := Simplex.vertex (semifreeCofiberZeroObject f))
            (y := Simplex.vertex (semifreeSuspensionObject X)) (cofiberToSuspensionMap f)) ≫
        eqToHom (congrArg SSet.HomotopyCategory.mk (semifreeSuspensionSquare_vertex X).symm) := by
  obtain ⟨hx, hy, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp
    (semifreeCofiberConnectingToSuspension_arrow f)
  exact hf

end SerrePositivity.InfinityCategories
