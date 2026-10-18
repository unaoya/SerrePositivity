module

public import SerrePositivity.InfinityCategories.DoldKanComparison.PathCubeImageCoordinates

/-!
# 有限内部座標の像と Path の写像

概要：選んだ内部座標の順序同型は、順序写像による Path の像と可換である。
方針：端点付きの集合の像を計算し、その等式の nerve を取る。
規約：端点と選んだ内部座標だけで厳密な順序を要求する。
使われ方：HA 1.3.1.16、Kerodon 2.5.9 の比較成分の単射な引き戻し。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory CategoryTheory.SimplicialThickening
variable {J K : Type u} [LinearOrder J] [LinearOrder K] {a b : J}

/-- 概要：Path の像は内部座標の有限像による立方体の写像を通る。
方針：端点と内部点の場合に分けて、二つの Path の頂点集合を比較する。
規約：順序写像の単射性は選んだ内部座標にだけ使う。
使われ方：Kerodon 2.5.9 の coherent 単体の引き戻しの自然性。 -/
lemma pathCubeMap_image (f : J →o K) (hab : a < b) (hfab : f a < f b)
    (S : Finset (Set.Ioo a b))
    (hS : ∀ t : S, f a < f t.val.val ∧ f t.val.val < f b)
    (hf : StrictMono (fun t : S ↦ f t.val.val)) :
    pathCubeMap hab S ≫ nerveMap (SimplicialThickening.functorMap f (.mk a) (.mk b)) =
      cubeImageMap (pathCubeImageIso f S hS hf) ≫
        pathCubeMap hfab (pathCubeImageSet f S hS) := by
  apply CategoryTheory.NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro F
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  let U := F.obj t
  apply CategoryTheory.SimplicialThickening.Path.ext
  apply Set.ext
  intro z
  change (z ∈ f '' {x | x = a ∨ x = b ∨ ∃ h : x ∈ Set.Ioo a b,
    (⟨x, h⟩ : Set.Ioo a b) ∈ (Subtype.val : S → Set.Ioo a b) '' U}) ↔
      (z = f a ∨ z = f b ∨ ∃ h : z ∈ Set.Ioo (f a) (f b),
        (⟨z, h⟩ : Set.Ioo (f a) (f b)) ∈
          (Subtype.val : ↥(pathCubeImageSet f S hS) → Set.Ioo (f a) (f b)) ''
            ((pathCubeImageIso f S hS hf) '' U))
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | ⟨hx, v, hv, he⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · have he' : v.val.val = x := congrArg Subtype.val he
      subst x
      exact Or.inr (Or.inr ⟨hS v, pathCubeImageIso f S hS hf v,
        ⟨v, hv, rfl⟩, rfl⟩)
  · intro hz
    rcases hz with rfl | rfl | ⟨hz, w, ⟨v, hv, hvw⟩, hw⟩
    · exact ⟨a, Or.inl rfl, rfl⟩
    · exact ⟨b, Or.inr (Or.inl rfl), rfl⟩
    · subst w
      exact ⟨v.val.val, Or.inr (Or.inr ⟨v.val.property, v, hv, rfl⟩),
        congrArg Subtype.val hw⟩

end SerrePositivity.InfinityCategories.DoldKanComparison
