module
public import SerrePositivity.InfinityCategories.Stable.CofiberTriangle
public import SerrePositivity.InfinityCategories.Stable.CofiberComparisonExt

/-! # 関手圏のホモトピー類から cofiber 三角形の射を作る

概要：cofiber 図式間の任意の h の射から、三角形の射を作って三成分を評価で計算する。
方針：射を関手辺で表し、その実際のホモトピーを既存の三角形の構成へ送る。
規約：成分は元の h の射の評価に一致する。使われ方：八面体の二つの比較の合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Pretriangulated MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：四角形の関手圏の h の射を表す実際のホモトピーを選ぶ。
方針：関手辺の類の全射性で辺を選び、uncurry する。
規約：両端の四角形を保持する。使われ方：合成した比較の三角形への転送。 -/
def squareHoHomotopy {X : SSet.{u}} [Quasicategory X]
    {F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X}
    (a : (SSet.HomotopyCategory.mk (functorVertex F) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (functorVertex G)) : SSet.Homotopy F G :=
  simplicialHomotopyOfFunctorEdge
    (Classical.choose (homotopyCategory_homMk_surjective (functorVertex F) (functorVertex G) a))

/-- 概要：選んだ四角形のホモトピーの類は指定した射そのもの。
方針：関手辺とホモトピーの往復を計算して選択条件を使う。
規約：代表辺の選択は類を変えない。使われ方：三成分と評価との一致。 -/
lemma squareHoHomotopy_homMk {X : SSet.{u}} [Quasicategory X]
    {F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X}
    (a : (SSet.HomotopyCategory.mk (functorVertex F) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (functorVertex G)) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (squareHoHomotopy a)) =
      a := by
  dsimp only [squareHoHomotopy]
  rw [stableFunctorEdge_homotopy_roundtrip]
  exact Classical.choose_spec
    (homotopyCategory_homMk_surjective (functorVertex F) (functorVertex G) a)

/-- 概要：選んだ比較の各角の自然変換成分は指定した h の射の評価。
方針：ホモトピーの評価と辺の類の一致を合成する。
規約：端点を Arrow の等号に含める。使われ方：三角形の射の三成分。 -/
lemma squareHoHomotopy_component_arrow {X : SSet.{u}} [Quasicategory X]
    {F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X}
    (a : (SSet.HomotopyCategory.mk (functorVertex F) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (functorVertex G)) (i j : Fin 2) :
    Arrow.mk ((homotopyNatTransOfEndpoints (squareHoHomotopy a).h
      (squareHoHomotopy a).h₀ (squareHoHomotopy a).h₁).app
        (SSet.HomotopyCategory.mk (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) i j))) =
      Arrow.mk ((squareDiagramHoEvaluation X i j).map a) := by
  have h := homotopyEvaluationOfEndpoints_arrow (squareHoHomotopy a)
    (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) i j)
  rw [squareHoHomotopy_homMk] at h
  exact h.symm

/-- 概要：cofiber 図式間の任意のホモトピー圏の射は cofiber 三角形の射を与える。
方針：選んだホモトピーから構成済みの射を作る。
規約：三角形の接続射を保持する。使われ方：八面体の合成した比較。 -/
def cofiberTriangleHoMap {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (t d : ZeroTriangle X) (ht : IsCofiberSequence t) (hd : IsCofiberSequence d)
    (a : (SSet.HomotopyCategory.mk (functorVertex t.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (functorVertex d.square)) :
    cofiberTriangle t ht ⟶ cofiberTriangle d hd :=
  cofiberTriangleMapOfHomotopy t d ht hd (squareHoHomotopy a)

/-- 概要：三角形の射の第一成分は左下の評価。
方針：代表ホモトピーの第一成分を評価と照合する。
規約：射の厳密な等号。使われ方：八面体の始点の射。 -/
lemma cofiberTriangleHoMap_hom₁ {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (t d : ZeroTriangle X) (ht : IsCofiberSequence t) (hd : IsCofiberSequence d)
    (a : (SSet.HomotopyCategory.mk (functorVertex t.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (functorVertex d.square)) :
    (cofiberTriangleHoMap t d ht hd a).hom₁ = (squareDiagramHoEvaluation X 0 0).map a := by
  apply Arrow.mk_injective
  exact squareHoHomotopy_component_arrow a 0 0

/-- 概要：三角形の射の第二成分は右下の評価。
方針：代表ホモトピーの第二成分を評価と照合する。
規約：射の厳密な等号。使われ方：八面体の中間対象の恒等成分。 -/
lemma cofiberTriangleHoMap_hom₂ {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (t d : ZeroTriangle X) (ht : IsCofiberSequence t) (hd : IsCofiberSequence d)
    (a : (SSet.HomotopyCategory.mk (functorVertex t.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (functorVertex d.square)) :
    (cofiberTriangleHoMap t d ht hd a).hom₂ = (squareDiagramHoEvaluation X 1 0).map a := by
  apply Arrow.mk_injective
  exact squareHoHomotopy_component_arrow a 1 0

/-- 概要：三角形の射の第三成分は右上の評価。
方針：代表ホモトピーの第三成分を評価と照合する。
規約：射の厳密な等号。使われ方：八面体の二つ目の cofiber 間の射。 -/
lemma cofiberTriangleHoMap_hom₃ {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (t d : ZeroTriangle X) (ht : IsCofiberSequence t) (hd : IsCofiberSequence d)
    (a : (SSet.HomotopyCategory.mk (functorVertex t.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (functorVertex d.square)) :
    (cofiberTriangleHoMap t d ht hd a).hom₃ = (squareDiagramHoEvaluation X 1 1).map a := by
  apply Arrow.mk_injective
  exact squareHoHomotopy_component_arrow a 1 1

end SerrePositivity.InfinityCategories
