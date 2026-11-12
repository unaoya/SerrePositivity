module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHorn

/-!
概要：inner fibration に沿う引き戻しの二射影は辺の可逆性を同時に反映する。
方針：第二成分の最後の外側ホーンを埋め、第一成分を相対外側ホーンで持ち上げる。
規約：全ての三つの圏は quasicategory、第一の関手だけに inner fibration 性を仮定する。
使われ方：Cat_∞ の引き戻し候補の core を関手 core の引き戻しへ比較する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：引き戻しの辺の両射影が可逆なら元の辺も可逆。
方針：第二成分の外側ホーン充填と第一関手の相対充填を合成する。
規約：第二関手に fibration 性を要求せず、inner fibration のみを使う。
使われ方：引き戻しと最大 Kan 部分複体の比較。 -/
lemma pullback_isInvertibleEdge_of_projections
    {E F B : SSet.{u}} [Quasicategory E] [Quasicategory F] [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [InnerFibration p] {x y : (pullback p q) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (pullback p q)) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (pullback.fst p q))))
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (pullback.snd p q)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers e
  intro n σ hσ
  obtain ⟨g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_isInvertibleEdge _ hf n (σ ≫ pullback.snd p q)
    (congrArg (fun z ↦ (pullback.snd p q).app _ z) hσ)
  have hsq : (σ ≫ pullback.fst p q) ≫ p =
      (horn (n + 2) (Fin.last (n + 2))).ι ≫ (g ≫ q) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← hg, Category.assoc]
  have hfix : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((σ ≫ pullback.fst p q).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n))) := by
    have hh := congrArg (fun z ↦ (pullback.fst p q).app _ z) hσ
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((σ ≫ pullback.fst p q).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n)))
      (f := e.map ((truncation 2).map (pullback.fst p q))) hh).mpr he
  obtain ⟨f, hfrestrict, hfp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.innerFibration_lift_finalHorn p n (σ ≫ pullback.fst p q)
    (g ≫ q) hsq hfix
  refine ⟨pullback.lift f g hfp, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact hfrestrict
  · rw [Category.assoc, pullback.lift_snd]
    exact hg

/-- 概要：引き戻しの辺の可逆性は両射影の可逆性と同値。
方針：二射影による保存と、相対外側ホーンによる同時反映を合わせる。
規約：辺の両端点も元の引き戻し内で固定する。
使われ方：core の各一次制限の所属条件の判定。 -/
lemma pullback_isInvertibleEdge_iff
    {E F B : SSet.{u}} [Quasicategory E] [Quasicategory F] [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [InnerFibration p] {x y : (pullback p q) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (pullback p q)) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (pullback.fst p q))) ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (pullback.snd p q))) :=
  ⟨fun he ↦ ⟨he.map _, he.map _⟩,
    fun h ↦ pullback_isInvertibleEdge_of_projections p q e h.1 h.2⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
