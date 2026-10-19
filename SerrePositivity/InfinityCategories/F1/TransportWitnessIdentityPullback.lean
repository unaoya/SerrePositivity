module

public import SerrePositivity.InfinityCategories.F1.TransportWitnessPullbackFunctor
public import SerrePositivity.InfinityCategories.F1.TransportWitnessTotalIso

/-!
概要：恒等底変換の表現空間を元の表現空間と厳密に同定する。
方針：恒等射に沿う pullback の第二射影の同型を使う。
規約：分類図式と全空間の写像を保つ。
使われ方：底上の降下の余錐の頂点を元の表現空間へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

local instance identityPullbackLF {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] : LeftFibration (pullback.fst (𝟙 B) p) :=
  ⟨leftFibrations.pullback_fst (𝟙 B) p (LeftFibration.mem (p := p))⟩

/-- 概要：恒等射に沿う底変換の射影は元の射影と全空間の同型で可換。
方針：pullback の可換条件の恒等射を消去する。
規約：同型の向きは pullback 全空間から元の全空間へ。
使われ方：表現空間の全空間同型を適用する。 -/
lemma transportIdentityPullback_comm {E B : SSet.{u + 1}} (p : E ⟶ B) :
    (asIso (pullback.snd (𝟙 B) p)).hom ≫ p = pullback.fst (𝟙 B) p := by
  simpa only [asIso_hom, Category.comp_id] using
    (pullback.condition (f := 𝟙 B) (g := p)).symm

/-- 概要：元の表現空間は恒等底変換における降下関手の値と厳密に同型。
方針：恒等底変換の全空間の同型による前合成を使う。
規約：表現の存在の仮定は不要。
使われ方：骨格の逆極限の頂点を元の表現空間と同定する。 -/
def transportWitnessIdentityPullbackIso {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] : transportWitnessSpace p ≅
      (transportWitnessPullbackFunctor p).obj (Opposite.op (Over.mk (𝟙 B))) :=
  transportWitnessTotalIso (pullback.fst (𝟙 B) p) p
    (asIso (pullback.snd (𝟙 B) p)) (transportIdentityPullback_comm p)

end SerrePositivity.InfinityCategories
