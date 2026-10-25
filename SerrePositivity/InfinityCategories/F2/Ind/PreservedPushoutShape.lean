module

public import SerrePositivity.InfinityCategories.F2.Ind.PreservedCoconeGluing
public import SerrePositivity.InfinityCategories.Core.PushoutCommonExtension

/-!
概要：部分図式と点 span の余極限保存から、元の形状 pushout の余極限保存を導く。
方針：保存された共通部分を両側に付加し、指定全余錐を貼って点 span へ制限する。
規約：元の全図式・元の関手・各指定余錐の像を同時に保持する。
使われ方：I-2 d′ の交換述語を全有限形状へ延長する帰納段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 単射側を持つ形状 pushout 上で、同じ全余極限を保存する余錐が存在する。 -/
lemma hasPreservedColimit_pushout_shape {A B C X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (f : A ⟶ B) (g : A ⟶ C) [Mono g] (F : pushout f g ⟶ X)
    (hA : HasPreservedColimit U (f ≫ (pushout.inl f g ≫ F)))
    (hB : HasPreservedColimit U (pushout.inl f g ≫ F))
    (hC : HasPreservedColimit U (pushout.inr f g ≫ F))
    (hs : ∀ s : pointConeSpan.{u} ⟶ X, HasPreservedColimit U s) :
    HasPreservedColimit U F := by
  obtain ⟨a, ha, hUa⟩ := hA
  let k := joinInl A (Δ[0] : SSet.{u})
  let GB := commonColimitDiagram a f (pushout.inl f g ≫ F) rfl
  have hg : g ≫ (pushout.inr f g ≫ F) = f ≫ (pushout.inl f g ≫ F) :=
    (pushout.condition_assoc F).symm
  let GC := commonColimitDiagram a g (pushout.inr f g ≫ F) hg
  obtain ⟨b, hb, hUb⟩ :=
    (hasPreservedColimit_commonDiagram_iff U a ha hUa f _ rfl).mpr hB
  obtain ⟨c, hc, hUc⟩ :=
    (hasPreservedColimit_commonDiagram_iff U a ha hUa g _ hg).mpr hC
  let i := pushout.inr f k
  let j := pushout.inr g k
  have he : i ≫ GB = j ≫ GC :=
    (commonColimitDiagram_cone a f _ rfl).trans
      (commonColimitDiagram_cone a g _ hg).symm
  let H := coneSpanCoconeGlue i j b c he
  let G := coneSpanBaseMap i j ≫ H
  have hleft : pushout.inl i j ≫ G = GB := by
    dsimp only [G]
    rw [← Category.assoc, coneSpanBaseMap_left, Category.assoc,
      coneSpanCoconeGlue_left, b.property]
  have hright : pushout.inr i j ≫ G = GC := by
    dsimp only [G]
    rw [← Category.assoc, coneSpanBaseMap_right, Category.assoc,
      coneSpanCoconeGlue_right, c.property]
  have : Mono j := Adhesive.mono_of_isPushout_of_mono_left
    (IsPushout.of_hasPushout g k)
  have hG : HasPreservedColimit U G :=
    hasPreservedColimit_coneSpanBase_of_pointSpan U (joinInr A Δ[0]) i j
      (rightConeTip_rightAnodyne A) H
      (coneSpanCoconeGlue_left_isColimit i j b c he hb)
      (coneSpanCoconeGlue_right_isColimit i j b c he hc)
      (coneSpanCoconeGlue_left_map_isColimit U i j b c he hUb)
      (coneSpanCoconeGlue_right_map_isColimit U i j b c he hUc) (hs _)
  have hcone : PushoutCommonExtension.inclusion f g k ≫ G = a.val := by
    simp only [PushoutCommonExtension.inclusion, Category.assoc]
    exact (congrArg (pushout.inr f k ≫ ·) hleft).trans
      (commonColimitDiagram_cone a f _ rfl)
  have hd : PushoutCommonExtension.map f g k ≫ G = F := by
    apply pushout.hom_ext
    · simp only [PushoutCommonExtension.map, pushout.inl_desc_assoc, Category.assoc]
      exact (congrArg (pushout.inl f k ≫ ·) hleft).trans
        (commonColimitDiagram_base a f _ rfl)
    · simp only [PushoutCommonExtension.map, pushout.inr_desc_assoc, Category.assoc]
      exact (congrArg (pushout.inl g k ≫ ·) hright).trans
        (commonColimitDiagram_base a g _ hg)
  have h := (hasPreservedColimit_iff_colimit_attachment U a ha hUa
    (f ≫ pushout.inl f g) (PushoutCommonExtension.inclusion f g k)
    (PushoutCommonExtension.map f g k) (PushoutCommonExtension.isPushout f g k) G hcone).mp hG
  rwa [hd] at h

end SerrePositivity.InfinityCategories.F2.Ind
