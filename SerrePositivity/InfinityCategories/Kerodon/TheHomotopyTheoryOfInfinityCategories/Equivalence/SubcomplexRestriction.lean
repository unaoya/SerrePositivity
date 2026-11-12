module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionFaceProjection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionPushoutGluing

/-!
概要：単体集合の射を部分複体へ制限し、同値性を二つの部分から貼り合わせる。
方針：制限射の包含との可換性を使い、交わりと和の pushout に既存の貼り合わせ補題を適用する。
規約：同値性は任意の quasicategory への前合成による条件。
使われ方：Kerodon Proposition 4.5.5.9（Tag 01FB）、Proposition 4.6.7.23（Tag 01LW）、解像の面の有限和。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：部分複体を別の部分複体に写す射の制限。
方針：包含と元の射の合成を部分複体へ持ち上げる。
規約：所属を保つ条件を preimage への包含で受け取る。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の和と交わりの上の射影。 -/
def subcomplexRestriction {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : X.Subcomplex) (B : Y.Subcomplex) (h : A ≤ B.preimage f) : A.toSSet ⟶ B.toSSet :=
  Subcomplex.lift (A.ι ≫ f) (by
    intro d y hy
    obtain ⟨x, rfl⟩ := hy
    exact h d x.property)

/-- 概要：制限射は包含の後で元の射に一致する。
方針：部分複体への持ち上げの値を取る。
規約：制限先の包含を後に合成する。
使われ方：Kerodon Proposition 4.5.5.9（Tag 01FB）、制限射の可換図式。 -/
lemma subcomplexRestriction_ι {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : X.Subcomplex) (B : Y.Subcomplex) (h : A ≤ B.preimage f) :
    subcomplexRestriction f A B h ≫ B.ι = A.ι ≫ f := rfl

/-- 概要：部分複体への制限は始域と終域の包含に自然。
方針：終域の包含の後で比較し、同じ元の射になることを使う。
規約：所属条件の証明の違いには依存しない。
使われ方：Kerodon Proposition 4.5.5.9（Tag 01FB）、貼り合わせの四つの可換式。 -/
lemma subcomplexRestriction_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    {A A' : X.Subcomplex} {B B' : Y.Subcomplex}
    (h : A ≤ B.preimage f) (h' : A' ≤ B'.preimage f) (hA : A ≤ A') (hB : B ≤ B') :
    Subcomplex.homOfLE hA ≫ subcomplexRestriction f A' B' h' =
      subcomplexRestriction f A B h ≫ Subcomplex.homOfLE hB := by
  apply (cancel_mono B'.ι).mp
  rw [Category.assoc, subcomplexRestriction_ι]
  rfl

/-- 概要：等しい部分複体を使った制限の前合成による同値性は一致する。
方針：二つの部分複体の等号を消去する。
規約：所属条件の証明は命題の証明の一意性で一致する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、交わりを別の面の和に書き換える手順。 -/
lemma subcomplexRestriction_isPrecompositionEquivalence_congr {X Y : SSet.{u}} (f : X ⟶ Y)
    {A A' : X.Subcomplex} {B B' : Y.Subcomplex}
    (h : A ≤ B.preimage f) (h' : A' ≤ B'.preimage f) (hA : A = A') (hB : B = B') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (subcomplexRestriction f A B h) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (subcomplexRestriction f A' B' h') := by
  subst A'
  subst B'
  rfl

/-- 概要：二つの部分とその交わりで制限射が同値なら和の上でも同値。
方針：二つの部分複体の交わりと和の pushout に前合成の同値性の貼り合わせを適用する。
規約：所属条件は各部分、交わり、和の四つを明示して受け取る。
使われ方：Kerodon Proposition 4.5.5.9（Tag 01FB）、Proposition 4.6.7.23（Tag 01LW）、有限の面の貼り合わせ。 -/
lemma subcomplexRestriction_isPrecompositionEquivalence_sup {X Y : SSet.{u}} (f : X ⟶ Y)
    (A₁ A₂ : X.Subcomplex) (B₁ B₂ : Y.Subcomplex)
    (h₁ : A₁ ≤ B₁.preimage f) (h₂ : A₂ ≤ B₂.preimage f)
    (hI : A₁ ⊓ A₂ ≤ (B₁ ⊓ B₂).preimage f)
    (hU : A₁ ⊔ A₂ ≤ (B₁ ⊔ B₂).preimage f)
    (eI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (subcomplexRestriction f _ _ hI))
    (e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (subcomplexRestriction f _ _ h₁))
    (e₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (subcomplexRestriction f _ _ h₂)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (subcomplexRestriction f _ _ hU) := by
  let sqA : Subcomplex.BicartSq (A₁ ⊓ A₂) A₁ A₂ (A₁ ⊔ A₂) := ⟨rfl, rfl⟩
  let sqB : Subcomplex.BicartSq (B₁ ⊓ B₂) B₁ B₂ (B₁ ⊔ B₂) := ⟨rfl, rfl⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_pushout_gluing sqA.isPushout sqB.isPushout
    (subcomplexRestriction f _ _ hI) (subcomplexRestriction f _ _ h₁)
    (subcomplexRestriction f _ _ h₂) (subcomplexRestriction f _ _ hU)
    (subcomplexRestriction_naturality f hI h₁ sqA.le₁₂ sqB.le₁₂)
    (subcomplexRestriction_naturality f hI h₂ sqA.le₁₃ sqB.le₁₃)
    (subcomplexRestriction_naturality f h₁ hU sqA.le₂₄ sqB.le₂₄)
    (subcomplexRestriction_naturality f h₂ hU sqA.le₃₄ sqB.le₃₄) eI e₁ e₂

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
