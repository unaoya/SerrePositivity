module

public import SerrePositivity.InfinityCategories.Sheaves.SetLocalEquivalence
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
概要：集合値の局所単射性を、同じ核対の対角射の局所全射性へ接続する。
方針：対角射の像篩は二つの成分の等化篩であることを、元の引き戻しの全射で示す。
規約：HTT 6.2.2.6 の局所性への通常圏の入力。核対は Mathlib の同じ pullback。
使われ方：S8 の単射でない局所同値を扱うための対角の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}

/-- 元の対角射の第一成分は恒等射。 -/
lemma presheafDiagonal_fst_apply (φ : P ⟶ Q) (U : Cᵒᵖ) (p : P.obj U) :
    (pullback.fst φ φ).app U ((pullback.diagonal φ).app U p) = p :=
  congrArg (fun η => η.app U p) (pullback.diagonal_fst φ)

/-- 元の対角射の第二成分も恒等射。 -/
lemma presheafDiagonal_snd_apply (φ : P ⟶ Q) (U : Cᵒᵖ) (p : P.obj U) :
    (pullback.snd φ φ).app U ((pullback.diagonal φ).app U p) = p :=
  congrArg (fun η => η.app U p) (pullback.diagonal_snd φ)

/-- 対角射の元の像篩は、核対の二つの成分の同じ等化篩。 -/
lemma imageSieve_diagonal (φ : P ⟶ Q) {U : C}
    (q : (pullback φ φ).obj (Opposite.op U)) :
    CategoryTheory.Presheaf.imageSieve (pullback.diagonal φ) q =
      CategoryTheory.Presheaf.equalizerSieve (F := P) (X := Opposite.op U)
        ((pullback.fst φ φ).app (Opposite.op U) q)
        ((pullback.snd φ φ).app (Opposite.op U) q) := by
  ext V f
  change (∃ p, (pullback.diagonal φ).app (Opposite.op V) p = (pullback φ φ).map f.op q) ↔
    P.map f.op ((pullback.fst φ φ).app _ q) =
      P.map f.op ((pullback.snd φ φ).app _ q)
  constructor
  · rintro ⟨p, hp⟩
    calc
      _ = (pullback.fst φ φ).app _ ((pullback φ φ).map f.op q) :=
        ((pullback.fst φ φ).naturality_apply f.op q).symm
      _ = (pullback.fst φ φ).app _ ((pullback.diagonal φ).app _ p) := congrArg _ hp.symm
      _ = p := presheafDiagonal_fst_apply φ _ p
      _ = (pullback.snd φ φ).app _ ((pullback.diagonal φ).app _ p) :=
        (presheafDiagonal_snd_apply φ _ p).symm
      _ = (pullback.snd φ φ).app _ ((pullback φ φ).map f.op q) := congrArg _ hp
      _ = _ := (pullback.snd φ φ).naturality_apply f.op q
  · intro h
    let p := P.map f.op ((pullback.fst φ φ).app _ q)
    refine ⟨p, ?_⟩
    have hb := ((evaluation Cᵒᵖ (Type u)).obj (Opposite.op V)).map_isPullback
      (IsPullback.of_hasPullback φ φ)
    apply PullbackCone.IsLimit.type_ext hb.isLimit
    · exact (presheafDiagonal_fst_apply φ _ p).trans
        ((pullback.fst φ φ).naturality_apply f.op q).symm
    · exact (presheafDiagonal_snd_apply φ _ p).trans
        (h.trans ((pullback.snd φ φ).naturality_apply f.op q).symm)

/-- 局所単射の同じ核対の対角射は局所全射。 -/
instance diagonal_isLocallySurjective (J : GrothendieckTopology C) (φ : P ⟶ Q)
    [CategoryTheory.Presheaf.IsLocallyInjective J φ] :
    CategoryTheory.Presheaf.IsLocallySurjective J (pullback.diagonal φ) where
  imageSieve_mem {U} q := by
    rw [imageSieve_diagonal]
    apply CategoryTheory.Presheaf.equalizerSieve_mem J φ
    exact congrArg (fun η => η.app (Opposite.op U) q) (pullback.condition (f := φ) (g := φ))

end SerrePositivity.InfinityCategories.Sheaves
