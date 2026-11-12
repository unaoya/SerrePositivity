module

public import SerrePositivity.KST.Spectra.SpectrumLevelwiseInverse
public import SerrePositivity.KST.Spectra.PointedComponentIsomorphism

/-!
概要：比較の逆方向の射と単位の自然性を結合する一般的な成分の計算。
方針：大きな有理化対象を展開せず、任意の BF 射と点つき射の図式で合成を計算する。
規約：全ての等式は実際の写像空間の連結成分で述べる。
使われ方：Goerss–Jardine I §7、BF 1978 §2。有理化の単位の自然性の検査。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：比較の逆方向の射を経由した二つの射を比較へ戻すと元の合成と同じ成分。
方針：逆方向の射の右ホモトピー逆に元の二つの射を前合成する。
規約：BF 対象と射は任意。
使われ方：BF 1978 §2、HTT A.3.3。有理化の射の比較への射影。 -/
theorem OmegaSpectrum.inverseComposite_projection_component
    {A B C D : OmegaSpectrum.{u}} (p : C ⟶ D)
    (hp : ∀ k, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (p.app k).right) (a : A ⟶ B) (b : B ⟶ D) (n : ℕ) :
    PointedMapping.componentOf ((a ≫ b ≫ levelwiseInverse p hp).app n ≫ p.app n) =
      PointedMapping.componentOf ((a ≫ b).app n) := by
  have h := PointedMapping.componentOf_comp_left
    (levelwiseInverse_right_component p hp n) (a.app n ≫ b.app n)
  change PointedMapping.componentOf
    ((a.app n ≫ b.app n ≫ (levelwiseInverse p hp).app n) ≫ p.app n) =
      PointedMapping.componentOf (a.app n ≫ b.app n)
  simpa only [Category.assoc, Category.comp_id] using h

/-- 概要：模型の単位・注入射・比較への射影の可換式から合成単位の自然性を得る。
方針：標的の全基点 π_* 同型を打ち消し、三つの成分の等式をつなぐ。
規約：対象は点つき単体集合、必要な二つの標的だけ Kan。
使われ方：Goerss–Jardine I §7、BF 1978 §2。単位の自然性の一般的な合成計算。 -/
theorem PointedMapping.compositeUnit_natural
    {A B C D E F P Q : PointedSimplicialSet.{u}}
    [KanComplex F.right] [KanComplex Q.right]
    (f : A ⟶ B) (a : A ⟶ C) (b : B ⟶ D) (t : C ⟶ D)
    (i : C ⟶ E) (j : D ⟶ F) (p : E ⟶ P) (q : F ⟶ Q)
    (r : P ⟶ Q) (m : E ⟶ F) (hq : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism q.right)
    (h₁ : componentOf (f ≫ b) = componentOf (a ≫ t))
    (h₂ : componentOf (i ≫ p ≫ r) = componentOf (t ≫ j ≫ q))
    (h₃ : componentOf (m ≫ q) = componentOf (p ≫ r)) :
    componentOf (f ≫ (b ≫ j)) = componentOf ((a ≫ i) ≫ m) := by
  apply componentOf_cancel_post_piIsomorphism q hq
  have h₁' := componentOf_comp_right h₁ (j ≫ q)
  have h₂' := componentOf_comp_left h₂ a
  have h₃' := componentOf_comp_left h₃ (a ≫ i)
  simp only [Category.assoc] at h₁' h₂' h₃' ⊢
  exact h₁'.trans (h₂'.symm.trans h₃'.symm)

end

end SerrePositivity.KST.Spectra
