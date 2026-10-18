module

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLiftingClosure
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Kan fibration の filtered colimit

概要：horn に対する右持ち上げ性は arrow 圏の filtered colimit で保たれる。
方針：horn と標準単体の有限表示可能性を使い、持ち上げ問題を一つの段階へ因子化する。
規約：Moss arXiv:1506.04887v2 Proposition 3.12 の Ex∞ の fibration 保存への補助。
使われ方：有限反復 Ex の Kan fibration の順序余極限。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SSet.modelCategoryQuillen
attribute [local instance] Cardinal.fact_isRegular_aleph0

/--
概要：Kan fibration の filtered な arrow の余極限は Kan fibration である。
方針：各 horn 生成射の両端の有限表示可能性に、持ち上げ性の余極限保存を適用する。
規約：図式の添字の宇宙と単体集合の値の宇宙を揃える。
使われ方：自然数の順序列の宇宙を持ち上げた適用。
-/
theorem hornRight_filteredColimit {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ Arrow SSet.{u}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ j, SSet.modelCategoryQuillen.J.rlp (F.obj j).hom) :
    SSet.modelCategoryQuillen.J.rlp c.pt.hom := by
  have : IsCardinalFiltered J Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff J).mpr inferInstance
  have hdom : ∀ i : SSet.modelCategoryQuillen.J.{u}.toSet,
      IsCardinalPresentable i.val.left Cardinal.aleph0.{u} := by
    rintro ⟨⟨A, B, f⟩, hf⟩
    change SSet.modelCategoryQuillen.J f at hf
    simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
    obtain ⟨n, ⟨k⟩⟩ := hf
    change IsCardinalPresentable (SSet.horn.{u} (n + 1) k).toSSet Cardinal.aleph0.{u}
    infer_instance
  have hcod : ∀ i : SSet.modelCategoryQuillen.J.{u}.toSet,
      IsCardinalPresentable i.val.right Cardinal.aleph0.{u} := by
    rintro ⟨⟨A, B, f⟩, hf⟩
    change SSet.modelCategoryQuillen.J f at hf
    simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
    obtain ⟨n, ⟨k⟩⟩ := hf
    change IsCardinalPresentable (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 1)))
      Cardinal.aleph0.{u}
    infer_instance
  exact @SerrePositivity.Smith.AccessibleLiftingClosure.rlp_of_isColimit.{u, u, u + 1}
    SSet.{u} _ _ SSet.modelCategoryQuillen.J.{u} Cardinal.aleph0.{u} _ hdom hcod J _ _ F c hc hF

/--
概要：Kan fibration の自然数添字の arrow の余極限は Kan fibration である。
方針：添字の宇宙を AsSmall で揃え、filtered colimit の結果を移す。
規約：単体集合の値の宇宙は任意。
使われ方：Ex∞ の自然数の反復列。
-/
theorem hornRight_sequentialColimit {F : ℕ ⥤ Arrow SSet.{u}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ n, SSet.modelCategoryQuillen.J.rlp (F.obj n).hom) :
    SSet.modelCategoryQuillen.J.rlp c.pt.hom := by
  let e := (AsSmall.equiv.{0, 0, u} (C := ℕ)).symm
  have : IsFiltered (AsSmall.{u} ℕ) :=
    IsFiltered.of_equivalence (AsSmall.equiv.{0, 0, u} (C := ℕ))
  exact hornRight_filteredColimit (J := AsSmall.{u} ℕ) (F := e.functor ⋙ F)
    (c := c.whisker e.functor) (hc.whiskerEquivalence e) (fun n => hF (e.functor.obj n))

end SerrePositivity.KST.Comparison
