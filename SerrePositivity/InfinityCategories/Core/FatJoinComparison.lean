module

public import SerrePositivity.InfinityCategories.Core.FatJoin
public import SerrePositivity.InfinityCategories.Core.JoinBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：fat join から通常の join への比較射。
方針：区間を二つの零単体の join と見て、左右の直積との比較を合成する。
規約：両因子上で恒等となる比較を取る。
使われ方：Kerodon Notation 4.6.2.3、Theorem 4.6.2.8。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右側の一点の直積因子を補う射。
方針：恒等射と標準零単体への定値射を組にする。
規約：補う一点は Δ[0]。
使われ方：Kerodon §4.6.2 の区間の端点の比較。 -/
noncomputable def pointTensorSection (A : SSet.{u}) : A ⟶ A ⊗ (Δ[0] : SSet.{u}) :=
  lift (𝟙 A) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))

/-- 概要：区間を二点の join に戻すと零端は左包含。
方針：標準単体の join の左頂点の計算で同型を打ち消す。
規約：点の補い方は pointTensorSection。
使われ方：Kerodon §4.6.2 の比較射の零端。 -/
lemma intervalJoin_zero (A : SSet.{u}) :
    SSet.ι₀ (X := A) ≫ (A ◁ (joinStdSimplexIso 0 0).inv) =
      pointTensorSection A ≫ (A ◁ joinInl (Δ[0] : SSet.{u}) Δ[0]) := by
  have h : (pointTensorSection A ≫ (A ◁ joinInl (Δ[0] : SSet.{u}) Δ[0])) ≫
      (A ◁ (joinStdSimplexIso 0 0).hom) = SSet.ι₀ := by
    rw [Category.assoc, ← whiskerLeft_comp, joinStdSimplexIso_inl_vertex]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro a
    apply Prod.ext
    · rfl
    · apply stdSimplex.ext
      intro i
      rfl
  have h' := congrArg (fun f ↦ f ≫ (A ◁ (joinStdSimplexIso 0 0).inv)) h
  simpa only [Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id,
    whiskerLeft_id, Category.comp_id] using h'.symm

/-- 概要：区間を二点の join に戻すと一端は右包含。
方針：標準単体の join の右頂点の計算で同型を打ち消す。
規約：点の補い方は pointTensorSection。
使われ方：Kerodon §4.6.2 の比較射の一端。 -/
lemma intervalJoin_one (A : SSet.{u}) :
    SSet.ι₁ (X := A) ≫ (A ◁ (joinStdSimplexIso 0 0).inv) =
      pointTensorSection A ≫ (A ◁ joinInr (Δ[0] : SSet.{u}) Δ[0]) := by
  have h : (pointTensorSection A ≫ (A ◁ joinInr (Δ[0] : SSet.{u}) Δ[0])) ≫
      (A ◁ (joinStdSimplexIso 0 0).hom) = SSet.ι₁ := by
    rw [Category.assoc, ← whiskerLeft_comp, joinStdSimplexIso_inr_vertex]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro a
    apply Prod.ext
    · rfl
    · apply stdSimplex.ext
      intro i
      rfl
  have h' := congrArg (fun f ↦ f ≫ (A ◁ (joinStdSimplexIso 0 0).inv)) h
  simpa only [Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id,
    whiskerLeft_id, Category.comp_id] using h'.symm

/-- 概要：二つの単体集合の円柱を通常の join へ写す射。
方針：区間の join 表示と左右の直積の比較を合成する。
規約：円柱の順序は (A×Δ[1])×B。
使われ方：Kerodon Notation 4.6.2.3 の比較射の円柱上の表示。 -/
noncomputable def joinCylinderMap (A B : SSet.{u}) :
    (A ⊗ (Δ[1] : SSet.{u})) ⊗ B ⟶ join A B :=
  ((A ◁ (joinStdSimplexIso 0 0).inv) ▷ B) ≫
    (joinTensorLeft A Δ[0] Δ[0] ▷ B) ≫ joinTensorRight (A ⊗ Δ[0]) Δ[0] B ≫
      joinMap (fst A Δ[0]) (snd Δ[0] B)

/-- 概要：円柱から join への射の零端は第一射影後の左包含。
方針：区間の左端と左右の比較射の左包含上の計算を使う。
規約：零端では B の成分を忘れる。
使われ方：Kerodon Notation 4.6.2.3 の貼り合わせの整合性。 -/
lemma joinCylinderMap_zero (A B : SSet.{u}) :
    (SSet.ι₀ (X := A) ▷ B) ≫ joinCylinderMap A B = fst A B ≫ joinInl A B := by
  have h : (SSet.ι₀ (X := A) ▷ B) ≫ ((A ◁ (joinStdSimplexIso 0 0).inv) ▷ B) ≫
      (joinTensorLeft A Δ[0] Δ[0] ▷ B) =
      (pointTensorSection A ▷ B) ≫ (joinInl (A ⊗ Δ[0]) Δ[0] ▷ B) := by
    change ((SSet.ι₀ (X := A) ≫ (A ◁ (joinStdSimplexIso 0 0).inv) ≫
      joinTensorLeft A Δ[0] Δ[0]) ▷ B) = _
    rw [← Category.assoc, intervalJoin_zero, Category.assoc, joinTensorLeft_inl]
    rfl
  simp only [← Category.assoc] at h
  unfold joinCylinderMap
  rw [← Category.assoc (SSet.ι₀ (X := A) ▷ B),
    ← Category.assoc ((SSet.ι₀ (X := A) ▷ B) ≫ _), h]
  simp only [Category.assoc]
  rw [← Category.assoc (joinInl (A ⊗ Δ[0]) Δ[0] ▷ B), joinTensorRight_inl]
  simp only [Category.assoc]
  rw [joinInl_joinMap]
  rfl

/-- 概要：円柱から join への射の一端は第二射影後の右包含。
方針：区間の右端と左右の比較射の右包含上の計算を使う。
規約：一端では A の成分を忘れる。
使われ方：Kerodon Notation 4.6.2.3 の貼り合わせの整合性。 -/
lemma joinCylinderMap_one (A B : SSet.{u}) :
    (SSet.ι₁ (X := A) ▷ B) ≫ joinCylinderMap A B = snd A B ≫ joinInr A B := by
  have h : (SSet.ι₁ (X := A) ▷ B) ≫ ((A ◁ (joinStdSimplexIso 0 0).inv) ▷ B) ≫
      (joinTensorLeft A Δ[0] Δ[0] ▷ B) =
      ((pointTensorSection A ≫ snd A Δ[0]) ▷ B) ≫
        (joinInr (A ⊗ Δ[0]) Δ[0] ▷ B) := by
    change ((SSet.ι₁ (X := A) ≫ (A ◁ (joinStdSimplexIso 0 0).inv) ≫
      joinTensorLeft A Δ[0] Δ[0]) ▷ B) = _
    rw [← Category.assoc, intervalJoin_one, Category.assoc, joinTensorLeft_inr]
    rfl
  simp only [← Category.assoc] at h
  unfold joinCylinderMap
  rw [← Category.assoc (SSet.ι₁ (X := A) ▷ B),
    ← Category.assoc ((SSet.ι₁ (X := A) ▷ B) ≫ _), h]
  simp only [Category.assoc]
  rw [← Category.assoc (joinInr (A ⊗ Δ[0]) Δ[0] ▷ B), joinTensorRight_inr]
  rw [joinInr_joinMap]
  rfl

/-- 概要：fat join から通常の join への比較射。
方針：円柱上の比較射を両端の整合性により pushout に降ろす。
規約：両因子上で既存の join の包含と一致する。
使われ方：Kerodon Notation 4.6.2.3、Theorem 4.6.2.8 の比較射。 -/
@[kerodon 01HR, kerodon 01HV]
noncomputable def fatJoinComparison (A B : SSet.{u}) : fatJoin A B ⟶ join A B :=
  fatJoinDesc (joinInl A B) (joinInr A B) (joinCylinderMap A B)
    (joinCylinderMap_zero A B) (joinCylinderMap_one A B)

/-- 概要：fat join の比較射は円柱上で joinCylinderMap に一致する。
方針：fat join の貼り合わせの円柱上の計算を使う。
規約：因子の順序は (A×Δ[1])×B。
使われ方：Kerodon Theorem 4.6.2.8 の比較の計算。 -/
lemma fatJoinCylinder_comparison (A B : SSet.{u}) :
    fatJoinCylinder A B ≫ fatJoinComparison A B = joinCylinderMap A B :=
  fatJoinCylinder_desc _ _ _ _ _

/-- 概要：fat join の比較射は左因子上で通常の左包含。
方針：貼り合わせの左因子上の計算を使う。
規約：左因子の頂点と単体を保つ。
使われ方：Kerodon Theorem 4.6.2.8 の相対的な比較。 -/
lemma fatJoinInl_comparison (A B : SSet.{u}) :
    fatJoinInl A B ≫ fatJoinComparison A B = joinInl A B :=
  fatJoinInl_desc _ _ _ _ _

/-- 概要：fat join の比較射は右因子上で通常の右包含。
方針：貼り合わせの右因子上の計算を使う。
規約：右因子の図式を固定する。
使われ方：Kerodon Theorem 4.6.2.8、Example 4.6.6.8。 -/
lemma fatJoinInr_comparison (A B : SSet.{u}) :
    fatJoinInr A B ≫ fatJoinComparison A B = joinInr A B :=
  fatJoinInr_desc _ _ _ _ _

end SerrePositivity.InfinityCategories
