module
public import SerrePositivity.KST.SConstruction.PerfectStableProductHomClass
public import SerrePositivity.InfinityCategories.F1B.Fibrations.EdgeRepresentativeLift
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.ArrowEndpointPair
public import SerrePositivity.InfinityCategories.F2.CatInfinity.QCatTensorAndArrowObjects

/-!
概要：安定圏の ∞ 圏の区間図式の自己比較を、両端で厳密に恒等な代表へ直す。
方針：両端の射の類を直積の忠実性で同時に検出し、既存の inner 射の代表持ち上げを使う。
規約：元区間図式と全比較の射の類を保持。新しい充填公理は導入しない。
使われ方：実右面の上下全比較の共有対角を固定端点の零 Hom へ戻す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 概要：両端で恒等な区間自己比較は、両端を全単体で恒等に固定した同じ類の代表を持つ。
方針：直積両射影の類を検出し、元両端評価の inner fibration で代表を修正する。
規約：全自己比較の類を保持。使われ方：共有対角の全比較の一意性への還元。 -/
lemma stableArrowLoop_endpointRepresentative_exists
    (f : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u})
    (e : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u + 1})).obj _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}))
      (functorVertex f) (functorVertex f))
    (h₀ : SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map
      (evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))) =
        SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
    (h₁ : SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map
      (evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))) =
        SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _)) :
    ∃ e' : SSet.Truncated.Edge
        (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u + 1})).obj _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}))
        (functorVertex f) (functorVertex f),
      (e'.map ((truncation 2).map (F2.arrowEndpointPair _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}))).edge =
        (SSet.Truncated.Edge.id
          ((F2.arrowEndpointPair _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}).app _ (functorVertex f))).edge ∧
      SSet.Truncated.HomotopyCategory.homMk e' = SSet.Truncated.HomotopyCategory.homMk e := by
  letI : Quasicategory (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⊗ _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}) :=
    F2.quasicategory_tensor _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}
  apply F1B.exists_kanEdgeRepresentative_lift (F2.arrowEndpointPair _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}) e
    (SSet.Truncated.Edge.id _)
  apply stableInfinityProduct_homMk_eq_of_projections
  · change SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map
      (evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))) =
        SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _)
    exact h₀
  · change SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map
      (evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))) =
        SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _)
    exact h₁
end SerrePositivity.KST.SConstruction
