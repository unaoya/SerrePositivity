module

public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
概要：有限な全空間を持つ底上の単体集合は、底上の圏でも有限表示である。
方針：忘却後の filtered 余極限で射を因子分解し、可換条件を元の余錐から戻す。
規約：底は任意、有限性は全空間だけに課す。添字の宇宙は単体集合と同じ。
使われ方：底を保つ左ホーン付加関手の filtered 余極限保存。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentable

local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩

/-- 有限な全空間を持つ底上の対象は、同じ宇宙の filtered 余極限に対し有限表示。 -/
instance finiteOver_isFinitelyPresentable {A B : SSet.{u}} (a : A ⟶ B) [A.Finite] :
    IsFinitelyPresentable.{u} (Over.mk a) := by
  apply IsCardinalPresentable.mk
  intro J _ _ F c hc
  have : IsFiltered J := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
  let hc' := isColimitOfPreserves (Over.forget B) hc
  constructor
  · intro g
    obtain ⟨j, f, hf⟩ := IsFinitelyPresentable.exists_hom_of_isColimit (X := A) hc' g.left
    change f ≫ (c.ι.app j).left = g.left at hf
    have hb : f ≫ (F.obj j).hom = a := by
      calc
        f ≫ (F.obj j).hom = f ≫ ((c.ι.app j).left ≫ c.pt.hom) :=
          congrArg (fun k ↦ f ≫ k) (c.ι.app j).w.symm
        _ = (f ≫ (c.ι.app j).left) ≫ c.pt.hom := (Category.assoc _ _ _).symm
        _ = g.left ≫ c.pt.hom := congrArg (fun k ↦ k ≫ c.pt.hom) hf
        _ = a := g.w
    refine ⟨j, Over.homMk f hb, ?_⟩
    exact Over.OverMorphism.ext hf
  · intro j f g h
    obtain ⟨j', t, ht⟩ := IsCardinalPresentable.exists_eq_of_isColimit' (X := A) Cardinal.aleph0
      hc' f.left g.left (congrArg (fun k ↦ k.left) h)
    exact ⟨j', t, Over.OverMorphism.ext ht⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentable
