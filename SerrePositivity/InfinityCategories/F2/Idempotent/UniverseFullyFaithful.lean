module

public import SerrePositivity.InfinityCategories.F1.Universe.PinchedHom
public import SerrePositivity.InfinityCategories.F1.Universe.Homotopy
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulCalculus

/-!
概要：元の関手の充満忠実性は宇宙持ち上げで保存される。
方針：元の全 pinched Hom の宇宙同型と、同じ元の写像の自然性を使用する。
規約：元の対象間の写像空間全体を比較し、π₀ だけで代用しない。
使われ方：持ち上げた全部分圏包含に沿う前層値の左 Kan 延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の単射は、各次数の同じ単射を持ち上げても単射。 -/
lemma idemUliftMap_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono ((SSet.uliftFunctor.{v, u}).map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b hab
  apply ULift.ext
  have hf : Function.Injective (f.app n) := (mono_iff_injective _).mp
    ((NatTrans.mono_iff_mono_app f).mp inferInstance n)
  exact hf (congrArg ULift.down hab)

/-- 元の全写像空間による充満忠実性は、任意の宇宙の持ち上げで保たれる。 -/
lemma IsFullyFaithful.ulift {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : IsFullyFaithful f) :
    IsFullyFaithful ((SSet.uliftFunctor.{v, u}).map f) := by
  rintro ⟨x⟩ ⟨y⟩
  have ha : IsSimplicialHomotopyEquivalence
      ((SSet.uliftFunctor.{v, u}).map (pinchedHomMap f x y)) := (hf x y).ulift
  let eb := qCatEquivalenceOfIso (uliftPinchedHomIso.{u, v} (f.app _ x) (f.app _ y))
  have hb : IsSimplicialHomotopyEquivalence
      (uliftPinchedHomIso.{u, v} (f.app _ x) (f.app _ y)).hom :=
    eb.isQCatEquivalence.isSimplicialHomotopyEquivalence
  have h := ha.comp hb
  rw [uliftPinchedHomIso_naturality] at h
  let ec := qCatEquivalenceOfIso (uliftPinchedHomIso.{u, v} x y)
  have hc : IsSimplicialHomotopyEquivalence (uliftPinchedHomIso.{u, v} x y).hom :=
    ec.isQCatEquivalence.isSimplicialHomotopyEquivalence
  exact hc.cancel_left h

end SerrePositivity.InfinityCategories.F2.Idempotent
