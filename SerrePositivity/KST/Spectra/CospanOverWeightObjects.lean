module

public import SerrePositivity.KST.Spectra.CospanNerveHornIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan

/-!
概要：cospan の BK 重みの中央と両端の over 圏を、元の cospan と一点として記述する。
方針：中央への射の一意性と、両端へ入る射が恒等だけであることを使う。
規約：全て元の over 圏の対象・射を保持する。使われ方：BK 重みとホーン重みの自然同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra

/-- 小さい cospan の平行射は一致する。 -/
instance smallCospanHom_subsingleton (a b : AsSmall.{u} WalkingCospan) :
    Subsingleton (a ⟶ b) :=
  ⟨fun _ _ ↦ by apply ULift.ext; exact Subsingleton.elim _ _⟩

/-- 小さい cospan の over 圏の平行射も一致する。 -/
instance smallCospanOverHom_subsingleton (t : AsSmall.{u} WalkingCospan)
    (a b : Over t) : Subsingleton (a ⟶ b) :=
  ⟨fun _ _ ↦ Over.OverMorphism.ext (Subsingleton.elim _ _)⟩

/-- 小さい cospan の共通終点は終対象。 -/
def cospanOne_isTerminal : IsTerminal (AsSmall.up.obj WalkingCospan.one :
    AsSmall.{u} WalkingCospan) :=
  IsTerminal.ofUniqueHom
    (fun a ↦ by
      rcases a with ⟨a⟩
      cases a with
      | none => exact 𝟙 _
      | some a =>
          cases a with
          | left => exact AsSmall.up.map WalkingCospan.Hom.inl
          | right => exact AsSmall.up.map WalkingCospan.Hom.inr)
    (fun _ _ ↦ by apply ULift.ext; exact Subsingleton.elim _ _)

/-- cospan の始点の over 圏の対象は、その始点上の恒等射だけ。 -/
lemma cospanOverEndpoint_eq (k : WalkingPair)
    (a : Over (AsSmall.up.obj (.some k : WalkingCospan) : AsSmall.{u} WalkingCospan)) :
    a = Over.mk (𝟙 (AsSmall.up.obj (.some k : WalkingCospan) : AsSmall.{u} WalkingCospan)) := by
  rcases a with ⟨⟨a⟩, ⟨⟩, ⟨f⟩⟩
  change WidePullbackShape.Hom a (.some k) at f
  cases f
  rfl

/-- 始点の over 圏の対象は一意。 -/
instance cospanOverEndpoint_subsingleton (k : WalkingPair) :
    Subsingleton (Over (AsSmall.up.obj (.some k : WalkingCospan) :
      AsSmall.{u} WalkingCospan)) :=
  ⟨fun a b ↦ (cospanOverEndpoint_eq k a).trans (cospanOverEndpoint_eq k b).symm⟩

/-- thin な圏の終対象上の over 圏は、忘却関手そのものの nerve で元の nerve と厳密同型。 -/
def nerveOverTerminalIso {C : Type u} [SmallCategory C]
    [∀ a b : C, Subsingleton (a ⟶ b)] (t : C) (ht : IsTerminal t) :
    nerve (Over t) ≅ nerve C where
  hom := nerveMap (Over.forget t)
  inv := nerveMap (Over.equivalenceOfIsTerminal ht).inverse
  hom_inv_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro σ
    refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
    · change (Over.equivalenceOfIsTerminal ht).inverse.obj (σ.obj i).left = σ.obj i
      rcases σ.obj i with ⟨a, ⟨⟩, f⟩
      change Over.mk (ht.from a) = Over.mk f
      congr 1
      exact ht.hom_ext _ _
    · intro i j f
      apply Over.OverMorphism.ext
      exact Subsingleton.elim _ _
  inv_hom_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro σ
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    exact Subsingleton.elim _ _

/-- 対象・射が一意な圏の nerve は、標準零単体と厳密同型。 -/
def nerveSingletonIso {C : Type u} [SmallCategory C] [Subsingleton C]
    [∀ a b : C, Subsingleton (a ⟶ b)] (c : C) : nerve C ≅ (Δ[0] : SSet.{u}) where
  hom := stdSimplex.isTerminalObj₀.from _
  inv := SSet.const (ComposableArrows.mk₀ c)
  hom_inv_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro σ
    refine CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _) ?_
    intro i j f
    exact Subsingleton.elim _ _
  inv_hom_id := stdSimplex.isTerminalObj₀.hom_ext _ _

end SerrePositivity.KST.Spectra
