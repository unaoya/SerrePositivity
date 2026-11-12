module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredTotalDetection
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SimultaneousTotalDetection

/-!
概要：同じ filtered ∞ 圏上の二つの coherent 空間値図式の余極限模型を元の共通段で有限検出する。
方針：二つの小さい unstraightening の同時検出を、各 fiber の元の値の比較で移す。
規約：strict 図式への置換を使わず、元の二つの有限射へのホモトピーを保つ。
使われ方：一般 coherent filtered 余極限の有限積・引き戻し比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]

/-- 概要：二つの coherent 余極限模型への有限射は元の共通の頂点の二つの値で表示できる。
方針：小さい全空間の同時 fiber 検出を元の値に移し、fiber 比較の逆合成をホモトピーで消す。
規約：元の二図式と全有限パラメータを保持。使われ方：有限極限交換の同時有限検出。 -/
lemma coherentFilteredTotalKan_pair_value_detection
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    {K L : SSet.{u}} [K.Finite] [L.Finite]
    (f : K ⟶ coherentDiagramTotalKan F) (g : L ⟶ coherentDiagramTotalKan G) :
    ∃ b : B _⦋0⦌,
      ∃ s : K ⟶ (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up b))).obj,
      ∃ t : L ⟶ (spaceInfinityObject (G.app (Opposite.op ⦋0⦌) (ULift.up b))).obj,
        Nonempty (SSet.Homotopy f (s ≫ coherentDiagramValueToTotalKan F b)) ∧
        Nonempty (SSet.Homotopy g (t ≫ coherentDiagramValueToTotalKan G b)) := by
  have move (C : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
      {A : SSet.{u}} (r : A ⟶ coherentDiagramTotalKan C) (b : B _⦋0⦌)
      (s : A ⟶ vertexFiber (smallLeftUnstraighteningProjection C) b)
      (H : Nonempty (SSet.Homotopy r (s ≫ vertexFiberι (smallLeftUnstraighteningProjection C) b ≫
        continuousKanReplacementUnit.app (smallLeftUnstraightening C)))) :
      Nonempty (SSet.Homotopy r
        ((s ≫ (smallLeftUnstraighteningFiberValueEquivalence C b).hom) ≫
          coherentDiagramValueToTotalKan C b)) := by
    let e := smallLeftUnstraighteningFiberValueEquivalence C b
    have h₀ := (functorVertex_piZero_eq_iff_homotopy _ _).mpr H
    have h₁ := (functorVertex_piZero_eq_iff_homotopy _ _).mpr
      ⟨functorHomotopyPostcomp (functorHomotopyPrecomp e.homInvIso.simplicialHomotopy s)
        (vertexFiberι (smallLeftUnstraighteningProjection C) b ≫
          continuousKanReplacementUnit.app (smallLeftUnstraightening C))⟩
    simp only [Category.assoc, Category.id_comp] at h₁
    apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
    simpa only [coherentDiagramValueToTotalKan, Category.assoc] using h₀.trans h₁.symm
  obtain ⟨b, s, t, Hs, Ht⟩ := continuousKanLeftFibration_pair_finite_fiber_detection
    (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G) f g
  exact ⟨b, s ≫ (smallLeftUnstraighteningFiberValueEquivalence F b).hom,
    t ≫ (smallLeftUnstraighteningFiberValueEquivalence G b).hom, move F f b s Hs, move G g b t Ht⟩

end SerrePositivity.InfinityCategories.F2
