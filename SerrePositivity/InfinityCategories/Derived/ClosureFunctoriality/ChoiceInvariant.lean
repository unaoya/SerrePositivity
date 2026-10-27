module
public import SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.ClosureFunctor

/-!
概要：同型によって存在述語が同値になるとき、同じ Classical.choose の代表は一致する。
方針：述語外延性と証明無関係性で選択を比較する。
規約：比較同型そのものや、関手の全 Hom 作用の一致は結論しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded

/-- 同値な存在述語は、同じ型の上で同じ選択を持つ。 -/
lemma existsChoose_eq_of_predicate_iff {I : Sort u} {P Q : I → Prop}
    (hP : ∃ i, P i) (hQ : ∃ i, Q i) (h : ∀ i, P i ↔ Q i) :
    hP.choose = hQ.choose := by
  have he : P = Q := funext (fun i => propext (h i))
  subst Q
  rfl

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (S : Set (ModuleCategory R D)) (M N : ModuleCategory R D)

/-- 実同型な二つの像は、同じ strict-range 述語の選択で同じ対象代表を得る。 -/
lemma dgModuleStrictRange_choose_eq_of_iso (e : M ≅ N)
    (hM : dgModuleStrictRange R D S M) (hN : dgModuleStrictRange R D S N) :
    hM.choose = hN.choose := by
  apply existsChoose_eq_of_predicate_iff hM hN
  intro P
  constructor
  · rintro ⟨hP, ⟨a⟩⟩
    exact ⟨hP, ⟨a ≪≫ e⟩⟩
  · rintro ⟨hP, ⟨a⟩⟩
    exact ⟨hP, ⟨a ≪≫ e.symm⟩⟩

variable (C : Type w) [DGCategory R C] [Small.{u} C]
  (F G : DGFunctor R (RightModule R C) (RightModule R D))
  (T : Set (ModuleCategory R C))
  (hF : ∀ M, T M → dgModuleStrictRange R D S (F.onClosed.obj M))
  (hG : ∀ M, T M → dgModuleStrictRange R D S (G.onClosed.obj M))

/-- ofRange の対象選択は、入力の対象別実同型に沿って厳密に一致する。 -/
lemma DGModuleStrictImage.ofRange_obj_eq_of_iso
    (M : {M // T M}) (a : F.onClosed.obj M.val ≅ G.onClosed.obj M.val) :
    (DGModuleStrictImage.ofRange R C D F T S hF).obj M =
      (DGModuleStrictImage.ofRange R C D G T S hG).obj M := by
  apply Subtype.ext
  exact dgModuleStrictRange_choose_eq_of_iso R D S _ _ a (hF M.val M.property)
    (hG M.val M.property)

section Family
variable [PreservesColimitsOfSize.{u, u} F.onClosed]
  [PreservesColimitsOfSize.{u, u} G.onClosed]
  {O : Type u} [LinearOrder O] [WellFoundedLT O] [Nonempty O]
  (hO : ∀ s : ℕ → O, ∃ b, ∀ n, s n < b)
  (B : DGProjectiveModuleFamily R C) (E : DGProjectiveModuleFamily R D)
  (hBF : ∀ i, ∃ j, Nonempty (F.onClosed.obj (B.2 i).val ≅ (E.2 j).val))
  (hBG : ∀ i, ∃ j, Nonempty (G.onClosed.obj (B.2 i).val ≅ (E.2 j).val))

/-- D-3 が実際に使用する閉包添字の選択も、像の実同型に沿って一致する。 -/
lemma dgProjectiveClosureFamilyImage_index_eq_of_iso
    (i : (dgProjectiveClosureFamily R C (T := O) B).1)
    (a : F.onClosed.obj ((dgProjectiveClosureFamily R C (T := O) B).2 i).val ≅
      G.onClosed.obj ((dgProjectiveClosureFamily R C (T := O) B).2 i).val) :
    (dgProjectiveClosureFamilyImage R C D F hO B E hBF).index i =
      (dgProjectiveClosureFamilyImage R C D G hO B E hBG).index i := by
  change (dgProjectiveClosureFamily_extension_image R C D F hO B E hBF i).choose =
    (dgProjectiveClosureFamily_extension_image R C D G hO B E hBG i).choose
  apply existsChoose_eq_of_predicate_iff
  intro j
  constructor
  · rintro ⟨e⟩
    exact ⟨a.symm ≪≫ e⟩
  · rintro ⟨e⟩
    exact ⟨a ≪≫ e⟩
/-- 閉包関手の対象作用も一致する。全 Hom の一致までは主張しない。 -/
lemma dgProjectiveClosureFunctor_obj_eq_of_iso
    (a : ∀ i : (dgProjectiveClosureFamily R C (T := O) B).1,
      F.onClosed.obj ((dgProjectiveClosureFamily R C (T := O) B).2 i).val ≅
        G.onClosed.obj ((dgProjectiveClosureFamily R C (T := O) B).2 i).val)
    (M : {M // dgProjectiveFamilyObjects R C
      (dgProjectiveClosureFamily R C (T := O) B) M}) :
    (dgProjectiveClosureFunctor R C D F B E hO hBF).obj M =
      (dgProjectiveClosureFunctor R C D G B E hO hBG).obj M := by
  apply Subtype.ext
  change ((dgProjectiveClosureFamily R D (T := O) E).2
    ((dgProjectiveClosureFamilyImage R C D F hO B E hBF).index M.property.choose)).val =
    ((dgProjectiveClosureFamily R D (T := O) E).2
      ((dgProjectiveClosureFamilyImage R C D G hO B E hBG).index M.property.choose)).val
  rw [dgProjectiveClosureFamilyImage_index_eq_of_iso R D C F G hO B E hBF hBG
    M.property.choose (a M.property.choose)]

end Family

end SerrePositivity.InfinityCategories
