module
public import SerrePositivity.InfinityCategories.Stable.SymmetricCoconeBranches
public import SerrePositivity.InfinityCategories.F1.CoconeMappingGluing

/-! # 対称 span 全体の余錐空間の自己引き戻し表示

概要：対称 span の余錐空間は、同じ辺の余錐空間の始点上の自己引き戻しと同型。
方針：両枝を同じ辺に揃え、余錐族の貼り合わせの存在と一意性を使う。
規約：値域の充填性や零対象性は不要。使われ方：ループ模型への比較の始域を全体の余錐空間に戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：対称 span の余錐空間への射は同じ辺に揃えた両枝で決まる。
方針：表示変更の同型を打ち消し、span の二枝での一意性に戻す。
規約：パラメータは任意。使われ方：自己引き戻し表示の一意性。 -/
lemma symmetricCoconeBranches_hom_ext {X T : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌)
    {a b : T ⟶ coconeMappingSpace (edgeSpan f f) y}
    (h₁ : a ≫ symmetricCoconeFirst f y = b ≫ symmetricCoconeFirst f y)
    (h₂ : a ≫ symmetricCoconeSecond f y = b ≫ symmetricCoconeSecond f y) : a = b := by
  apply coconeMappingSpace_hom_ext_of_pushout horn₂₀.isPushout (edgeSpan f f) y
  · apply (cancel_mono (eqToHom (congrArg (fun q => coconeMappingSpace q y)
      (edgeSpan_left f f)))).1
    exact h₁
  · apply (cancel_mono (eqToHom (congrArg (fun q => coconeMappingSpace q y)
      (edgeSpan_right f f)))).1
    exact h₂

/-- 概要：共通始点で一致する二つの指定辺の余錐族は対称 span 全体へ貼り合わさる。
方針：両枝の表示を元へ戻し、join で展開した貼り合わせを使う。
規約：同じ辺の余錐空間を両方の入力に使う。使われ方：自己引き戻し表示の存在部分。 -/
lemma exists_symmetricCoconeBranches_glue {X T : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌)
    (b c : T ⟶ coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y)
    (h : b ≫ coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y =
      c ≫ coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y) :
    ∃ a : T ⟶ coconeMappingSpace (edgeSpan f f) y,
      a ≫ symmetricCoconeFirst f y = b ∧ a ≫ symmetricCoconeSecond f y = c := by
  let b' := b ≫ eqToHom (congrArg (fun q => coconeMappingSpace q y) (edgeSpan_left f f).symm)
  let c' := c ≫ eqToHom (congrArg (fun q => coconeMappingSpace q y) (edgeSpan_right f f).symm)
  have hh := congrArg (fun t => sliceUnderUncurry (t ≫ vertexFiberι
    (sliceUnderProjection (stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge)) y)) h
  change sliceUnderUncurry ((b ≫ cosliceRestrictionFiberMap _ (stdSimplex.δ (1 : Fin 2)) y) ≫ _) =
    sliceUnderUncurry ((c ≫ cosliceRestrictionFiberMap _ (stdSimplex.δ (1 : Fin 2)) y) ≫ _) at hh
  have Hb := coconeMappingSpace_restrict_uncurry (SSet.yonedaEquiv.symm f.edge)
    (stdSimplex.δ (1 : Fin 2)) y b
  have Hc := coconeMappingSpace_restrict_uncurry (SSet.yonedaEquiv.symm f.edge)
    (stdSimplex.δ (1 : Fin 2)) y c
  have hhc := Hb.symm.trans (hh.trans Hc)
  have hh' : joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T) ≫ sliceUnderUncurry
      (b' ≫ vertexFiberι (sliceUnderProjection (horn₂₀.ι₀₁ ≫ edgeSpan f f)) y) =
    joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T) ≫ sliceUnderUncurry
      (c' ≫ vertexFiberι (sliceUnderProjection (horn₂₀.ι₀₂ ≫ edgeSpan f f)) y) := by
    have Hb' := congrArg (fun t => joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T) ≫ t)
      (coconeMappingSpace_change_uncurry (edgeSpan_left f f).symm y b)
    have Hc' := congrArg (fun t => joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T) ≫ t)
      (coconeMappingSpace_change_uncurry (edgeSpan_right f f).symm y c)
    exact Hb'.trans (hhc.trans Hc'.symm)
  obtain ⟨a, ha, hb⟩ := exists_coconeMappingSpace_glue horn₂₀.isPushout (edgeSpan f f) y b' c' hh'
  refine ⟨a, ?_, ?_⟩
  · change a ≫ (cosliceRestrictionFiberMap _ horn₂₀.ι₀₁ y ≫ _) = b
    rw [← Category.assoc, ha]
    dsimp only [b']
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  · change a ≫ (cosliceRestrictionFiberMap _ horn₂₀.ι₀₂ y ≫ _) = c
    rw [← Category.assoc, hb]
    dsimp only [c']
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- 概要：対称 span の余錐空間は同じ枝の余錐空間の自己引き戻し。
方針：可換性と貼り合わせの存在・一意性を使う。
規約：全パラメータの普遍性。使われ方：ループ模型との比較の同型。 -/
lemma symmetricCoconeBranches_isPullback {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    IsPullback (symmetricCoconeFirst f y) (symmetricCoconeSecond f y)
      (coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y)
      (coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y) := by
  apply IsPullback.mk' (symmetricCoconeBranches_comm f y)
  · intro T a b h₁ h₂
    exact symmetricCoconeBranches_hom_ext f y h₁ h₂
  · intro T b c h
    exact exists_symmetricCoconeBranches_glue f y b c h

/-- 概要：対称 span 全体の余錐空間から同じ枝の自己引き戻しへの標準同型。
方針：証明した引き戻しの普遍性から標準引き戻しとの比較同型を取る。
規約：順方向の両成分は二枝の制限。使われ方：枝の自己引き戻しのループ比較へ接続する。 -/
def symmetricCoconeKernelPairIso {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    coconeMappingSpace (edgeSpan f f) y ≅
      pullback (coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y)
        (coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y) :=
  (symmetricCoconeBranches_isPullback f y).isoPullback

end SerrePositivity.InfinityCategories
