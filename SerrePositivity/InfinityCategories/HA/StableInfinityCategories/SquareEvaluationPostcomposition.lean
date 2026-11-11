module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorHoEvaluation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonComposition

/-! # 四角形の h の射の評価と後合成

概要：四角形を後合成してから角で評価する操作は、角の成分の後合成に一致する。
方針：関手圏の射を辺で代表し、実際の一次単体の評価を計算する。
規約：端点表示を Arrow に含める。使われ方：D7 の包含後の成分の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 四角形の射の角での評価は後合成と可換。 -/
lemma squareDiagramHoEvaluation_postcomp_arrow {X Y : SSet.{u}} [Quasicategory X]
    (q : X ⟶ Y) {v w : ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) _⦋0⦌}
    (a : (SSet.HomotopyCategory.mk v :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk w) (i j : Fin 2) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation Y i j).map
      ((hoFunctor.map ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map q)).toFunctor.map a)) =
      Arrow.mk ((hoFunctor.map q).toFunctor.map ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X i j).map a)) := by
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective v w a
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
