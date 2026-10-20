module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeProductLifting

/-!
概要：全単射 RLP 射へ実ホモトピーを持ち上げ、元の両端と指定部分の全区間を保持する。
方針：端点境界と指定部分の pushout-product に、元の基底の二変数射を持ち上げる。
規約：源・標的の Kan 性やモデル構造は不要。使われ方：π 同型の写像 path 分解での反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial
namespace SerrePositivity.KST.Spectra

/-- 端点境界の同じ貼り合わせは、基底射への後合成と厳密に可換。 -/
lemma homotopyBoundaryMap_post {X E B : SSet.{u}} (f g : X ⟶ E) (p : E ⟶ B) :
    LargeParameterHomotopy.boundaryMap f g ≫ p =
      LargeParameterHomotopy.boundaryMap (f ≫ p) (g ≫ p) := by
  apply (LargeParameterHomotopy.boundaryColimit X).hom_ext
  rintro ⟨j⟩
  cases j
  · change X ◁ boundary.ι (1 : Fin 2) ≫ (LargeParameterHomotopy.boundaryMap f g ≫ p) =
      X ◁ boundary.ι (1 : Fin 2) ≫ LargeParameterHomotopy.boundaryMap (f ≫ p) (g ≫ p)
    rw [← Category.assoc, LargeParameterHomotopy.boundaryMap_zero,
      LargeParameterHomotopy.boundaryMap_zero, Category.assoc]
  · change X ◁ boundary.ι (0 : Fin 2) ≫ (LargeParameterHomotopy.boundaryMap f g ≫ p) =
      X ◁ boundary.ι (0 : Fin 2) ≫ LargeParameterHomotopy.boundaryMap (f ≫ p) (g ≫ p)
    rw [← Category.assoc, LargeParameterHomotopy.boundaryMap_one,
      LargeParameterHomotopy.boundaryMap_one, Category.assoc]

/-- 両端・基底の全区間・指定部分の全区間を保持する、元のホモトピーの実持ち上げ。 -/
structure RelativeHomotopyRlpLift {E B A X : SSet.{u}} (p : E ⟶ B) (i : A ⟶ X)
    {f g : X ⟶ E} (H : SSet.Homotopy (f ≫ p) (g ≫ p))
    (V : SSet.Homotopy (i ≫ f) (i ≫ g)) where
  homotopy : SSet.Homotopy f g
  over : homotopy.h ≫ p = H.h
  relative : i ▷ (Δ[1] : SSet.{u}) ≫ homotopy.h = V.h

/-- 二つの単射の相対持ち上げから、同じ基底ホモトピーを指定部分固定で持ち上げる。 -/
def RelativeHomotopyRlpLift.choose {E B A X : SSet.{u}} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p) (i : A ⟶ X) [Mono i]
    {f g : X ⟶ E} (H : SSet.Homotopy (f ≫ p) (g ≫ p))
    (V : SSet.Homotopy (i ≫ f) (i ≫ g))
    (hv : V.h ≫ p = i ▷ (Δ[1] : SSet.{u}) ≫ H.h) : RelativeHomotopyRlpLift p i H V := by
  have he : LargeParameterHomotopy.boundaryMap f g ≫ p =
      X ◁ (boundary 1).ι ≫ H.h := by
    rw [homotopyBoundaryMap_post, HomotopyEndpointComparison.boundary_eq H]
  let hex := RelativeProductLifting.exists_lift p hp i (boundary 1).ι
    (LargeParameterHomotopy.boundaryMap f g) V.h H.h
    (KanHomotopyExtension.boundary_compatibility i f g V) he hv
  let L := hex.choose
  have hL := hex.choose_spec
  refine ⟨{ h := L, h₀ := ?_, h₁ := ?_, rel := ?_ }, hL.2.2, hL.2.1⟩
  · rw [← LargeParameterHomotopy.section_zero X, Category.assoc,
      ← boundary.ι_ι (1 : Fin 2), whiskerLeft_comp, Category.assoc, hL.1,
      LargeParameterHomotopy.boundaryMap_zero]
    rfl
  · rw [← LargeParameterHomotopy.section_one X, Category.assoc,
      ← boundary.ι_ι (0 : Fin 2), whiskerLeft_comp, Category.assoc, hL.1,
      LargeParameterHomotopy.boundaryMap_one]
    rfl
  · ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

end SerrePositivity.KST.Spectra
