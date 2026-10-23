module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackMatchingLift
public import SerrePositivity.InfinityCategories.F1.Cocartesian.EdgeImageComparison

/-!
概要：quasicategory の底上で、底変換の第一射影は cocartesian 辺を保存・反映する。
方針：元の fibration から選ぶ同じ始点・底の lift と比較し、可逆な後半辺の合成を使う。
規約：底変換の射には単射性や充填性を要求しない。
使われ方：底の単体への引き戻しの元の cocartesian 辺の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- quasicategory の底への引き戻しの cocartesian 辺は、元の全空間でも cocartesian。 -/
lemma isCocartesianEdge_pullback_image_of_quasicategory_base {E A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    (f : A ⟶ B) (e : (pullback p f) _⦋1⦌) (he : IsCocartesianEdge (pullback.snd p f) e) :
    IsCocartesianEdge p ((pullback.fst p f).app (Opposite.op ⦋1⦌) e) := by
  obtain ⟨h, hs, hr, hh, hfirst⟩ := exists_cocartesianPullbackMatchingLift p f e
  exact isCocartesianEdge_image_of_matching_lift (pullback.snd p f) p
    (pullback.fst p f) e h he hh hs hr hfirst

/-- quasicategory の底では、元の cocartesian 性と底変換の cocartesian 性は厳密に一致する。 -/
lemma isCocartesianEdge_pullback_iff_of_quasicategory_base {E A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    (f : A ⟶ B) (e : (pullback p f) _⦋1⦌) :
    IsCocartesianEdge (pullback.snd p f) e ↔
      IsCocartesianEdge p ((pullback.fst p f).app (Opposite.op ⦋1⦌) e) :=
  ⟨isCocartesianEdge_pullback_image_of_quasicategory_base p f e,
    isCocartesianEdge_pullback p f e⟩

end SerrePositivity.InfinityCategories
