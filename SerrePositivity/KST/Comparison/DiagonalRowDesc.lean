module

public import SerrePositivity.KST.Comparison.DiagonalRowEvaluation

/-!
# 対角模型の行ごとの余極限表示の普遍性

概要：標準単体との積からの dinatural な射の族を、対角模型からの一意な射へまとめる。
方針：同じ次数の行で恒等単体を評価し、関係式で自然性と各行の復元を証明する。
規約：Segal 1974 Proposition 1.6 の対角模型への接続。fat realization の同値性とは別の主張。
使われ方：骨格の付着で構成した写像を、対角単体集合へ降ろす際の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial ConcreteCategory
open SerrePositivity.BisimplicialModel

variable (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) {Z : SSet.{u}}
    (ι : ∀ n : ℕ, F.obj (op ⦋n⦌) ⊗ Δ[n] ⟶ Z)
    (hι : ∀ {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌),
      (F.map θ.op ▷ Δ[m]) ≫ ι m = (F.obj (op ⦋n⦌) ◁ SSet.stdSimplex.map θ) ≫ ι n)

/--
概要：dinatural な行の射の族から対角模型への射を定める。
方針：各次数で恒等単体を使い、行の関係式と内側の自然性を合わせる。
規約：射の族は全ての単体圏の射について整合する。
使われ方：対角模型の余極限表示の存在。
-/
def diagonalRowDesc : diagonal.obj F ⟶ Z where
  app d := ↾fun x => (ι d.unop.len).app d (x, SSet.stdSimplex.objEquiv.symm (𝟙 d.unop))
  naturality {d e} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    have hh := congrArg (fun t => t.app e
      ((F.obj d).map θ x, SSet.stdSimplex.objEquiv.symm (𝟙 e.unop))) (hι θ.unop)
    have hn := congrArg (fun t => t
      ((x, SSet.stdSimplex.objEquiv.symm (𝟙 d.unop)) :
        (F.obj d ⊗ SSet.stdSimplex.obj d.unop).obj d)) ((ι d.unop.len).naturality θ)
    change (ι e.unop.len).app e
      ((F.obj e).map θ ((F.map θ).app d x), SSet.stdSimplex.objEquiv.symm (𝟙 e.unop)) =
      Z.map θ ((ι d.unop.len).app d (x, SSet.stdSimplex.objEquiv.symm (𝟙 d.unop)))
    calc
      _ = (ι e.unop.len).app e
          ((F.map θ).app e ((F.obj d).map θ x), SSet.stdSimplex.objEquiv.symm (𝟙 e.unop)) :=
        congrArg (fun y => (ι e.unop.len).app e
          (y, SSet.stdSimplex.objEquiv.symm (𝟙 e.unop)))
          (ConcreteCategory.congr_hom ((F.map θ).naturality θ) x).symm
      _ = (ι d.unop.len).app e
          ((F.obj d).map θ x, SSet.stdSimplex.objEquiv.symm θ.unop) := by
        change (ι e.unop.len).app e
          ((F.map θ).app e ((F.obj d).map θ x), SSet.stdSimplex.objEquiv.symm (𝟙 e.unop)) =
            (ι d.unop.len).app e ((F.obj d).map θ x,
              (SSet.stdSimplex.map θ.unop).app e (SSet.stdSimplex.objEquiv.symm (𝟙 e.unop))) at hh
        simpa only [← SSet.stdSimplex.objEquiv_symm_comp, Category.id_comp] using hh
      _ = _ := by
        change (ι d.unop.len).app e ((F.obj d).map θ x,
          (SSet.stdSimplex.obj d.unop).map θ (SSet.stdSimplex.objEquiv.symm (𝟙 d.unop))) =
            Z.map θ ((ι d.unop.len).app d
              (x, SSet.stdSimplex.objEquiv.symm (𝟙 d.unop))) at hn
        simpa only [SSet.stdSimplex.map_objEquiv_symm, Category.comp_id] using hn

/--
概要：対角模型へまとめた射の各行への制限は元の射の族に一致する。
方針：標準単体が表す射に dinatural な関係式を適用する。
規約：添字の射には全ての単体圏の射を使う。
使われ方：対角模型の余極限の射の計算則。
-/
@[reassoc] theorem diagonalRowEvaluation_desc (n : ℕ) :
    diagonalRowEvaluation F n ≫ diagonalRowDesc F ι hι = ι n := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  have hh := congrArg (fun t => t.app d
    (x, SSet.stdSimplex.objEquiv.symm (𝟙 d.unop)))
      (hι (SSet.stdSimplex.objEquiv t))
  change (ι d.unop.len).app d
    ((F.map (SSet.stdSimplex.objEquiv t).op).app d x,
      SSet.stdSimplex.objEquiv.symm (𝟙 d.unop)) =
      (ι n).app d (x, (SSet.stdSimplex.map (SSet.stdSimplex.objEquiv t)).app d
        (SSet.stdSimplex.objEquiv.symm (𝟙 d.unop))) at hh
  change (ι d.unop.len).app d
    ((F.map (SSet.stdSimplex.objEquiv t).op).app d x,
      SSet.stdSimplex.objEquiv.symm (𝟙 d.unop)) = (ι n).app d (x, t)
  simpa only [← SSet.stdSimplex.objEquiv_symm_comp, Category.id_comp,
    Equiv.symm_apply_apply] using hh

/--
概要：各行の制限を指定した対角模型からの射は一意である。
方針：各次数の元を、その次数の行と恒等単体の評価で表示する。
規約：存在の証明の選択には依存しない。
使われ方：対角模型の余極限の普遍性の一意性。
-/
theorem diagonalRowDesc_unique (f : diagonal.obj F ⟶ Z)
    (hf : ∀ n, diagonalRowEvaluation F n ≫ f = ι n) :
    f = diagonalRowDesc F ι hι := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  have h := congrArg (fun t => t.app d
    (x, SSet.stdSimplex.objEquiv.symm (𝟙 d.unop))) (hf d.unop.len)
  change f.app d ((diagonalRowEvaluation F d.unop.len).app d
    (x, SSet.stdSimplex.objEquiv.symm (𝟙 d.unop))) = _ at h
  rw [diagonalRowEvaluation_identity] at h
  exact h

end SerrePositivity.KST.Comparison
