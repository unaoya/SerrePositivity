module

public import SerrePositivity.InfinityCategories.DoldKanComparison.PathCubeImageMap

/-!
# coherent 成分の有限内部座標の像に対する自然性

概要：選んだ内部点を厳密単調に送る順序写像について、coherent 成分の引き戻しは像の成分に等しい。
方針：Path の写像を有限座標の順序同型で分解し、降順の立方体評価を移す。
規約：次数の異なる表示は HEq、指定した共通次数では等式で比較する。
使われ方：HA 1.3.1.16、Kerodon 2.5.9 の比較写像の単射な引き戻し。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]
variable {J K : Type u} [LinearOrder J] [LinearOrder K] {a b : J}

/-- 概要：引き戻した coherent Hom の立方体は像の座標の立方体から得られる。
方針：豊穣関手の合成の Hom 写像を開き、Path の有限像の分解を使う。
規約：有限像は実際の内部点の順序同型によって取る。
使われ方：Kerodon 2.5.9 の比較成分の自然性を評価前に示す。 -/
lemma coherentCubeHom_image
    (s : EnrichedFunctor SSet (SimplicialThickening K) (ClosedCategory R D))
    (f : J →o K) (hab : a < b) (hfab : f a < f b) (S : Finset (Set.Ioo a b))
    (hS : ∀ t : S, f a < f t.val.val ∧ f t.val.val < f b)
    (hf : StrictMono (fun t : S ↦ f t.val.val)) :
    coherentCubeHom ((SimplicialThickening.functor f).comp SSet s) hab S =
      cubeImageMap (pathCubeImageIso f S hS hf) ≫
        coherentCubeHom s hfab (pathCubeImageSet f S hS) := by
  change pathCubeMap hab S ≫
    (nerveMap (SimplicialThickening.functorMap f (.mk a) (.mk b)) ≫
      s.map (.mk (f a)) (.mk (f b))) = _
  rw [← Category.assoc, pathCubeMap_image f hab hfab S hS hf, Category.assoc]
  rfl

/-- 概要：選んだ有限内部点の像を取る操作は coherent 成分を保つ。
方針：座標同値で立方体評価を移し、移した降順番号付けの一意性を使う。
規約：像の濃度の表示による次数の差を HEq で吸収する。
使われ方：HA 1.3.1.16 の有限頂点集合上で単射な引き戻し。 -/
lemma coherentCubeComponent_image_heq
    (s : EnrichedFunctor SSet (SimplicialThickening K) (ClosedCategory R D))
    (f : J →o K) (hab : a < b) (hfab : f a < f b) (S : Finset (Set.Ioo a b))
    (hS : ∀ t : S, f a < f t.val.val ∧ f t.val.val < f b)
    (hf : StrictMono (fun t : S ↦ f t.val.val)) :
    HEq (coherentCubeComponent ((SimplicialThickening.functor f).comp SSet s) hab S)
      (coherentCubeComponent s hfab (pathCubeImageSet f S hS)) := by
  change HEq (cubeEvaluation (R := R) (D := D) (descendingEnumeration S)
    (coherentCubeHom ((SimplicialThickening.functor f).comp SSet s) hab S))
      (cubeEvaluation (R := R) (D := D) (descendingEnumeration (pathCubeImageSet f S hS))
        (coherentCubeHom s hfab (pathCubeImageSet f S hS)))
  have hhom := coherentCubeHom_image s f hab hfab S hS hf
  have heval := cubeEvaluation_imageMap (pathCubeImageIso f S hS hf).toEquiv
    (descendingEnumeration S) (coherentCubeHom s hfab (pathCubeImageSet f S hS))
  apply HEq.trans (heq_of_eq (congrArg
    (cubeEvaluation (R := R) (D := D) (descendingEnumeration S)) hhom))
  apply HEq.trans (heq_of_eq heval)
  exact cubeEvaluation_strictAnti_heq _
    ((pathCubeImageIso f S hS hf).strictMono.comp_strictAnti
      (descendingEnumeration_strictAnti S)) _

/-- 概要：共通次数で取った coherent 成分は有限内部座標の像に関して等しい。
方針：指定次数から標準次数への HEq を成分の自然性の両側に合成する。
規約：二つの次数証明に整合性の追加仮定はない。
使われ方：Kerodon 2.5.9 の dg 単体の hom フィールドの自然性。 -/
lemma coherentCubeComponentAt_image
    (s : EnrichedFunctor SSet (SimplicialThickening K) (ClosedCategory R D))
    (f : J →o K) (hab : a < b) (hfab : f a < f b) (S : Finset (Set.Ioo a b))
    (hS : ∀ t : S, f a < f t.val.val ∧ f t.val.val < f b)
    (hf : StrictMono (fun t : S ↦ f t.val.val)) (k : ℤ)
    (hk : k = -(S.card : ℤ)) (hl : k = -((pathCubeImageSet f S hS).card : ℤ)) :
    coherentCubeComponentAt ((SimplicialThickening.functor f).comp SSet s) hab S k hk =
      coherentCubeComponentAt s hfab (pathCubeImageSet f S hS) k hl := by
  exact eq_of_heq ((coherentCubeComponentAt_heq _ hab S k hk).trans
    ((coherentCubeComponent_image_heq s f hab hfab S hS hf).trans
      (coherentCubeComponentAt_heq s hfab _ k hl).symm))

end SerrePositivity.InfinityCategories.DoldKanComparison
