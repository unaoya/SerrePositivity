module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FiberHomotopyProjection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorHoEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathIso

/-! # 可縮な fiber による比較の射影

概要：trivial Kan fibration の同じ底の二つの持ち上げの標準比較は底で恒等となる。
方針：fiber の包含の射影は定値なので、h では全ての射が恒等射になる。
規約：端点の表示を Arrow の等号に含める。使われ方：完全関手の懸垂比較の正規化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：trivial Kan fibration の標準比較を後合成で底へ送ると恒等となる。
方針：比較の構成に使う関手の内部 Hom の fiber に射影の恒等式を適用する。
規約：始域・底への追加の quasicategory 仮定は不要。使われ方：懸垂比較の始点の計算。 -/
lemma functorIsoOfTrivialKanFibration_projection_arrow {A E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (f g : A ⟶ E)
    (h : f ≫ p = g ≫ p) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration p f g h) p).hom =
      Arrow.mk (𝟙 (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ p)) :
        hoFunctor.obj ((ihom A).obj B))) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    eqToIso.inv, eqToHom_refl, Category.id_comp, Category.comp_id]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map
  let q := (ihom A).map p
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ p)
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan q b
  haveI := hc.kanComplex
  dsimp only [Functor.mapIso]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.vertexFiberHo_projection_arrow q b _

/-- 概要：標準比較の各頂点の成分を底へ送るとその像の恒等射。
方針：関手の h での射影の恒等式を通常の関手の成分で評価する。
規約：全空間 E は quasicategory。使われ方：懸垂比較の始点成分の正規化。 -/
lemma functorIsoOfTrivialKanFibration_projection_component_arrow {A E B : SSet.{u}}
    [Quasicategory E] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (f g : A ⟶ E)
    (h : f ≫ p = g ≫ p) (x : A _⦋0⦌) :
    Arrow.mk ((hoFunctor.map p).toFunctor.map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration p f g h).toNatIso.hom.app
        (SSet.HomotopyCategory.mk x))) =
    Arrow.mk (𝟙 (SSet.HomotopyCategory.mk ((g ≫ p).app (Opposite.op ⦋0⦌) x) :
      hoFunctor.obj B)) := by
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation A B ⋙
    (evaluation (hoFunctor.obj A) (hoFunctor.obj B)).obj (SSet.HomotopyCategory.mk x)
  have he := congrArg V.mapArrow.obj
    (functorIsoOfTrivialKanFibration_projection_arrow p f g h)
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorIso_toNatIso_postcomp_hom_app]
  dsimp only [V, Functor.mapArrow_obj] at he
  change Arrow.mk (((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation A B).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration p f g h) p).hom).app
      (SSet.HomotopyCategory.mk x)) =
    Arrow.mk (((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation A B).map
      (𝟙 (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ p))))).app
      (SSet.HomotopyCategory.mk x)) at he
  erw [CategoryTheory.Functor.map_id] at he
  have hid : Arrow.mk (NatTrans.app (𝟙 ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation A B).obj
      (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ p))))) (SSet.HomotopyCategory.mk x)) =
      Arrow.mk (𝟙 (SSet.HomotopyCategory.mk ((g ≫ p).app (Opposite.op ⦋0⦌) x))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation_obj (g ≫ p)]
    rfl
  simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.toNatIso] using he.trans hid

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
