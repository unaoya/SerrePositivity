module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsUniverseLift

/-!
概要：集合値のULiftは、元の像篩・等化篩と局所全単射性を保存し反映する。
方針：同じ要素のup/downで篩を同定し、既存の局所全射性・局所単射性の条件へ渡す。
規約：HTT 6.2.2.7の集合値部分に使う既存の係数移送の法則。
  Kerodon §7.1（Tag 02H1）。小さい通常のsiteの集合値模型に限る。
使われ方：S8でsiteと係数の宇宙を変える際、元の局所同値の射を保持する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type v} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}

/-- 同じULiftの前後で、指定した要素の像篩は一致する。 -/
lemma imageSieve_ulift (φ : P ⟶ Q) {U : C}
    (s : ULift.{t} (Q.obj (Opposite.op U))) :
    CategoryTheory.Presheaf.imageSieve (Functor.whiskerRight φ uliftFunctor.{t, u}) s =
      CategoryTheory.Presheaf.imageSieve φ s.down := by
  ext V f
  change (∃ x : ULift.{t} (P.obj (Opposite.op V)),
    ULift.up (φ.app _ x.down) = ULift.up (Q.map f.op s.down)) ↔
      ∃ x : P.obj (Opposite.op V), φ.app _ x = Q.map f.op s.down
  constructor
  · rintro ⟨x, h⟩
    exact ⟨x.down, congrArg ULift.down h⟩
  · rintro ⟨x, h⟩
    exact ⟨ULift.up x, congrArg ULift.up h⟩

/-- 同じULiftの前後で、指定した二要素の等化篩は一致する。 -/
lemma equalizerSieve_ulift {U : Cᵒᵖ} (x y : ULift.{t} (P.obj U)) :
    CategoryTheory.Presheaf.equalizerSieve (F := P ⋙ uliftFunctor.{t, u}) x y =
      CategoryTheory.Presheaf.equalizerSieve (F := P) x.down y.down := by
  ext V f
  change ULift.up (P.map f.op x.down) = ULift.up (P.map f.op y.down) ↔
    P.map f.op x.down = P.map f.op y.down
  exact ⟨congrArg ULift.down, congrArg ULift.up⟩

/-- 元の同じ位相と射に対する局所全射性は、値のULiftで保存・反映される。 -/
lemma isLocallySurjective_ulift_iff (J : GrothendieckTopology C) (φ : P ⟶ Q) :
    CategoryTheory.Presheaf.IsLocallySurjective J
      (Functor.whiskerRight φ uliftFunctor.{t, u}) ↔
        CategoryTheory.Presheaf.IsLocallySurjective J φ := by
  constructor
  · intro h
    constructor
    intro U s
    simpa only [imageSieve_ulift] using
      (h.imageSieve_mem (U := U) (ULift.up s))
  · intro h
    constructor
    intro U s
    rw [imageSieve_ulift φ s]
    exact h.imageSieve_mem (U := U) s.down

/-- 元の同じ位相と射に対する局所単射性も、値のULiftで保存・反映される。 -/
lemma isLocallyInjective_ulift_iff (J : GrothendieckTopology C) (φ : P ⟶ Q) :
    CategoryTheory.Presheaf.IsLocallyInjective J
      (Functor.whiskerRight φ uliftFunctor.{t, u}) ↔
        CategoryTheory.Presheaf.IsLocallyInjective J φ := by
  constructor
  · intro h
    constructor
    intro U x y hxy
    simpa only [equalizerSieve_ulift] using
      (h.equalizerSieve_mem (ULift.up x) (ULift.up y) (congrArg ULift.up hxy))
  · intro h
    constructor
    intro U x y hxy
    rw [equalizerSieve_ulift x y]
    exact h.equalizerSieve_mem x.down y.down (congrArg ULift.down hxy)

end SerrePositivity.InfinityCategories.Sheaves
