module

public import SerrePositivity.KST.Comparison.FatDegreeNormalization

/-!
# fat realization の各次数の全射な標準形との同値

概要：fat realization の各次数の元は、全射な単体写像とその終域の行の元で一意に表せる。
方針：標準形を各行の包含へ戻し、正規化との両合成を面の関係式と余等化子の全射性で計算する。
規約：Segal 1974 Proposition 1.6、Appendix A。対角への比較の可逆性とは別の同値。
使われ方：有限骨格の単射性と各次数での生成元の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial ConcreteCategory

/--
概要：全射な標準形を fat realization の各次数へ戻す射。
方針：全射を標準単体の元と読み、対応する行の包含を使う。
規約：行の元と全射を同時に保持する。
使われ方：正規化の逆写像。
-/
def fatNormalFormRealize (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    FatNormalForm F d ⟶ (fatRealization F).obj d :=
  ↾fun p => (fatRealizationInclusion F p.degree.len).app d
    (p.simplex, SSet.stdSimplex.objEquiv.symm p.epi)

/--
概要：行の元を正規化してから戻すと、元の行からの包含に一致する。
方針：像の包含に関する面の関係式と、epi–mono 分解の合成を使う。
規約：元の標準単体の射に全射性は要求しない。
使われ方：余等化子全体での逆写像の計算。
-/
theorem fatNormalFormRealize_normalize (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (n : ℕ) (x : (F.obj (op ⦋n⦌)).obj d) (t : Δ[n].obj d) :
    fatNormalFormRealize F d (fatNormalize F d x (SSet.stdSimplex.objEquiv t)) =
      (fatRealizationInclusion F n).app d (x, t) := by
  let a := SSet.stdSimplex.objEquiv t
  let θ : SimplexFace := ⟨(image a).len, n, image.ι a,
    SimplexCategory.mono_iff_injective.mp inferInstance⟩
  have h := congrArg (fun k => k.app d
    (x, SSet.stdSimplex.objEquiv.symm (factorThruImage a))) (fatRealizationInclusion_face F θ)
  change fatNormalFormRealize F d (fatNormalize F d x a) =
    (fatRealizationInclusion F n).app d
      (x, (SSet.stdSimplex.map (image.ι a)).app d
        (SSet.stdSimplex.objEquiv.symm (factorThruImage a))) at h
  have ht : (SSet.stdSimplex.map (image.ι a)).app d
      (SSet.stdSimplex.objEquiv.symm (factorThruImage a)) = t := by
    rw [← SSet.stdSimplex.objEquiv_symm_comp, image.fac]
    exact Equiv.symm_apply_apply _ t
  rw [ht] at h
  exact h

/--
概要：標準形を各行から含めて正規化すると元の標準形に戻る。
方針：包含での正規化の計算則と、全射の正規化の復元を使う。
規約：全射性の証明の選択には依存しない。
使われ方：同値の右逆性。
-/
theorem fatDegreeNormalize_realize (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (p : FatNormalForm F d) :
    fatDegreeNormalize F d (fatNormalFormRealize F d p) = p := by
  change fatDegreeNormalize F d ((fatRealizationInclusion F p.degree.len).app d
    (p.simplex, SSet.stdSimplex.objEquiv.symm p.epi)) = p
  rw [fatDegreeNormalize_inclusion, Equiv.apply_symm_apply]
  exact fatNormalize_of_normalForm F d p

/--
概要：fat realization の各次数の元を正規化して戻すと元に戻る。
方針：余等化子の全射性で行の元の計算へ帰着する。
規約：標準形の一意性を仮定せず、余等化子の普遍性から導く。
使われ方：同値の左逆性。
-/
theorem fatNormalFormRealize_degreeNormalize (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (y : (fatRealization F).obj d) :
    fatNormalFormRealize F d (fatDegreeNormalize F d y) = y := by
  let : Epi (fatDegreeCofork F d).π := Cofork.IsColimit.epi (fatDegreeCoforkIsColimit F d)
  obtain ⟨⟨n, x, t⟩, rfl⟩ :=
    (CategoryTheory.epi_iff_surjective (fatDegreeCofork F d).π).mp inferInstance y
  change fatNormalFormRealize F d
    (fatDegreeNormalize F d ((fatRealizationInclusion F n).app d (x, t))) =
      (fatRealizationInclusion F n).app d (x, t)
  rw [fatDegreeNormalize_inclusion]
  exact fatNormalFormRealize_normalize F d n x t

/--
概要：fat realization の各次数と全射な標準形の型との同値。
方針：余等化子へ降ろした正規化と、各行の包含による復元を両逆とする。
規約：対角への比較の弱同値性をこの同値の内容には含めない。
使われ方：fat realization の骨格の各次数での具体的な表示。
-/
def fatNormalFormEquiv (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    (fatRealization F).obj d ≃ FatNormalForm F d where
  toFun := fatDegreeNormalize F d
  invFun := fatNormalFormRealize F d
  left_inv := fatNormalFormRealize_degreeNormalize F d
  right_inv := fatDegreeNormalize_realize F d

end SerrePositivity.KST.Comparison
