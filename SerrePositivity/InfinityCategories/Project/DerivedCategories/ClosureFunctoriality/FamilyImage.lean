module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.ExtensionRange
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGProjectiveClosureFamily

/-!
概要：基底間の実 dg 同型から、閉包族の添字写像と対象別同型を得る。
方針：閉包の演算閉性と段階帰納を使い、証明済みの像から添字を選ぶ。
規約：選択は一度だけ保持する。異なる入力関手間の厳密な選択整合性は主張しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (F : DGFunctor R (RightModule R C) (RightModule R D))
  [PreservesColimitsOfSize.{u, u} F.onClosed]
  {T : Type u} [LinearOrder T] [WellFoundedLT T] [Nonempty T]
  (hT : ∀ s : ℕ → T, ∃ b, ∀ n, s n < b)
  (B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R C) (E : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D)
  (hB : ∀ i, ∃ j, Nonempty (F.onClosed.obj (B.2 i).val ≅ (E.2 j).val))

include hT hB in
/-- 基底の strict 互換から、閉包の全対象について実 dg 同型を得る。 -/
lemma dgProjectiveClosureFamily_extension_image
    (i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily R C (T := T) B).1) :
    ∃ j : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily R D (T := T) E).1,
      Nonempty (F.onClosed.obj
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily R C (T := T) B).2 i).val ≅
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily R D (T := T) E).2 j).val) := by
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily R D (T := T) E
  let S : Set (ModuleCategory R D) := Set.range (fun j => (G.2 j).val)
  have hz : S (moduleZero R D) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_zero R D E
  have hs : ∀ M, S M → ∀ n : ℤ, S (M⟦n⟧) := by
    rintro _ ⟨j, rfl⟩ n
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_shift R D hT E n j
  have hb : ∀ M N, S M → S N → S (M ⨿ N) := by
    rintro _ _ ⟨j, rfl⟩ ⟨k, rfl⟩
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_binary R D hT E j k
  have hc : ∀ M N, S M → S N → ∀ f : M ⟶ N, S (moduleCone R D f) := by
    rintro _ _ ⟨j, rfl⟩ ⟨k, rfl⟩ f
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_cone R D hT E j k f
  have hn : ∀ M : ℕ → ModuleCategory R D, (∀ n, S (M n)) → S (∐ M) := by
    intro M hM
    choose j hj using hM
    obtain ⟨k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_countable R D hT E j
    exact ⟨k, hk.trans (congrArg (fun N : ℕ → ModuleCategory R D => ∐ N) (funext hj))⟩
  have hbase : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange R D S (F.onClosed.obj (B.2 j).val) := by
    intro j
    obtain ⟨k, ⟨e⟩⟩ := hB j
    obtain ⟨l, hl⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_base R D (T := T) E k
    exact ⟨(E.2 k).val, ⟨l, congrArg Subtype.val hl⟩, ⟨e.symm⟩⟩
  obtain ⟨N, ⟨j, rfl⟩, ⟨e⟩⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgProjectiveClosureStage_extension_strictRange R C D F S hz hs hb hc hn B hbase i.1 i.2
  exact ⟨j, ⟨e.symm⟩⟩

/-- 一つの関手について添字と実比較同型を一緒に保持する。 -/
structure DGProjectiveFamilyImage (B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R C)
    (E : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D) where
  index : B.1 → E.1
  iso : ∀ i, F.onClosed.obj (B.2 i).val ≅ (E.2 (index i)).val

/-- 帰納で証明した像から添字写像 φ とその実 dg 同型を選択する。 -/
def dgProjectiveClosureFamilyImage :
    DGProjectiveFamilyImage R C D F
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily R C (T := T) B)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily R D (T := T) E) where
  index i := (dgProjectiveClosureFamily_extension_image R C D F hT B E hB i).choose
  iso i := (dgProjectiveClosureFamily_extension_image R C D F hT B E hB i).choose_spec.some

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
