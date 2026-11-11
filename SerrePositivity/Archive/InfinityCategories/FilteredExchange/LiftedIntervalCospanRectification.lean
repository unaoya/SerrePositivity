module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanHomotopyRectification
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementPath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Homotopy

/-!
概要：元の小さい interval 置換の全 path を持ち上げ、大きい Kan cospan の左脚へ移す。
方針：元の標準円柱を宇宙移送し、指定した cospan 比較の中心成分で後合成する。
規約：小さい interval 置換自体を持ち上げる。使われ方：実 fiber と切断の厳密な比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits SSet
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.F2
variable {X Z : SSet.{u}} {E B : SSet.{max u v}}
  [KanComplex E] [KanComplex B] (f : X ⟶ Z) (p : E ⟶ B)
  [HomotopicalAlgebra.Fibration p]
  (s : (SSet.uliftFunctor.{v, u}).obj X ⟶ E)
  (t : (SSet.uliftFunctor.{v, u}).obj Z ⟶ B)
  (hs : (SSet.uliftFunctor.{v, u}).map f ≫ t = s ≫ p)
local notation "pr" => pullback.snd (NatTrans.app (intervalEndpointNatTrans 0) Z) f

include hs in
/-- 元の小さい全 path の持ち上げに中心成分を合成した指定ホモトピー。 -/
def liftedIntervalCospanHomotopy :
    SSet.Homotopy (((SSet.uliftFunctor.{v, u}).map pr ≫ s) ≫ p)
      ((SSet.uliftFunctor.{v, u}).map (intervalReplacementEndpoint f) ≫ t) := by
  let H := uliftSimplicialHomotopy.{u, v} (intervalReplacementPathHomotopy f (𝟙 _))
  refine { h := H.h ≫ t, h₀ := ?_, h₁ := ?_, rel := ?_ }
  · change _ = ((SSet.uliftFunctor.{v, u}).map pr ≫ s) ≫ p
    rw [← Category.assoc, H.h₀]
    simp only [Category.id_comp, Functor.map_comp]
    rw [Category.assoc, hs, ← Category.assoc]
  · change _ = (SSet.uliftFunctor.{v, u}).map (intervalReplacementEndpoint f) ≫ t
    rw [← Category.assoc, H.h₁]
    simp only [Category.id_comp]
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 左脚 fibration に沿って全 path を持ち上げた、厳密な新しい左成分。 -/
def liftedIntervalCospanLeft : (SSet.uliftFunctor.{v, u}).obj (intervalReplacement f) ⟶ E :=
  kanHomotopyRectification p ((SSet.uliftFunctor.{v, u}).map pr ≫ s)
    ((SSet.uliftFunctor.{v, u}).map (intervalReplacementEndpoint f) ≫ t)
    (liftedIntervalCospanHomotopy f p s t hs)

/-- 新しい左成分は、元の置換終点と同じ中心成分に厳密に写る。 -/
lemma liftedIntervalCospanLeft_over :
    liftedIntervalCospanLeft f p s t hs ≫ p =
      (SSet.uliftFunctor.{v, u}).map (intervalReplacementEndpoint f) ≫ t :=
  kanHomotopyRectification_over _ _ _ _

/-- 厳密化後の左成分と元の射影に続く左成分の指定同型。 -/
def liftedIntervalCospanLeftIso :
    FunctorIso ((SSet.uliftFunctor.{v, u}).map pr ≫ s) (liftedIntervalCospanLeft f p s t hs) :=
  kanHomotopyRectificationIso _ _ _ _

end SerrePositivity.InfinityCategories.F2
