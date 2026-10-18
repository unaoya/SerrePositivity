module

public import SerrePositivity.KST.Comparison.FatNormalForm
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# 各次数の余等化子へ降りる正規化

概要：全射な標準形への写像を fat realization の各次数の実際の余等化子へ降ろす。
方針：評価関手の余等化子保存と、面の二射での正規化の一致を使う。
規約：Segal 1974 Proposition 1.6、Appendix A の具体的な fat realization。
使われ方：標準形との同値と骨格の成分の計算。
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
概要：fat realization を固定次数で評価した余等化子の余錐。
方針：余等化子の射と条件を次数で評価する。
規約：対象は抽象的な余等化子の取り直しではなく、既存の fat realization の次数。
使われ方：各次数での正規化の desc。
-/
def fatDegreeCofork (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    Cofork ((fatRelationLeft F).app d) ((fatRelationRight F).app d) :=
  Cofork.ofπ ((coequalizer.π (fatRelationLeft F) (fatRelationRight F)).app d)
    (congrArg (fun t => t.app d) (coequalizer.condition (fatRelationLeft F) (fatRelationRight F)))

/--
概要：各次数で評価した fat realization の余錐は余等化子である。
方針：前層の次数での評価が余等化子を保つことを使う。
規約：型の圏における実際の普遍性。
使われ方：正規化とその計算則。
-/
def fatDegreeCoforkIsColimit (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    IsColimit (fatDegreeCofork F d) :=
  isColimitOfHasCoequalizerOfPreservesColimit
    ((evaluation SimplexCategoryᵒᵖ (Type u)).obj d) (fatRelationLeft F) (fatRelationRight F)

/--
概要：行の余積の固定次数から全射な標準形へ送る射。
方針：各成分の標準単体を epi–mono 分解する。
規約：単体の行の次数は依存和の添字から読む。
使われ方：余等化子へ降ろす前の正規化。
-/
def fatRowNormalize (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    (fatRowObject F).obj d ⟶ FatNormalForm F d :=
  ↾fun p => fatNormalize F d p.2.1 (SSet.stdSimplex.objEquiv p.2.2)

/--
概要：面の関係式の二射は、行の正規化へ合成すると等しくなる。
方針：標準単体の後合成と、面で不変な正規化の補題を使う。
規約：単射性は既存の単体圏の Mono 条件へ移す。
使われ方：正規化の余等化子への降下条件。
-/
theorem fatRowNormalize_condition (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) :
    (fatRelationLeft F).app d ≫ fatRowNormalize F d =
      (fatRelationRight F).app d ≫ fatRowNormalize F d := by
  apply ConcreteCategory.hom_ext
  rintro ⟨θ, x, t⟩
  let : Mono θ.hom := SimplexCategory.mono_iff_injective.mpr θ.injective
  change fatNormalize F d ((F.map θ.hom.op).app d x) (SSet.stdSimplex.objEquiv t) =
    fatNormalize F d x (SSet.stdSimplex.objEquiv ((SSet.stdSimplex.map θ.hom).app d t))
  have ht : SSet.stdSimplex.objEquiv ((SSet.stdSimplex.map θ.hom).app d t) =
      SSet.stdSimplex.objEquiv t ≫ θ.hom := rfl
  rw [ht]
  exact fatNormalize_face F d θ.hom x (SSet.stdSimplex.objEquiv t)

/--
概要：fat realization の各次数から全射な標準形への実際の正規化の射。
方針：面の二射の一致で、型の圏の余等化子へ降ろす。
規約：標準形が一意であることをこの定義の入力にはしない。
使われ方：標準形との同値の順方向。
-/
def fatDegreeNormalize (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    (fatRealization F).obj d ⟶ FatNormalForm F d :=
  Cofork.IsColimit.desc (fatDegreeCoforkIsColimit F d) (fatRowNormalize F d)
    (fatRowNormalize_condition F d)

/--
概要：正規化を余等化子の射に合成すると行の正規化になる。
方針：型の圏の余等化子の計算則を使う。
規約：全ての次数での射の等式。
使われ方：各行の包含での正規化の計算。
-/
theorem fatDegreeNormalize_π (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    (fatDegreeCofork F d).π ≫ fatDegreeNormalize F d = fatRowNormalize F d :=
  Cofork.IsColimit.π_desc' (fatDegreeCoforkIsColimit F d) _ _

/--
概要：各行から入れた元の正規化は、行と単体写像の直接の正規化である。
方針：余等化子の計算則を一つの依存和の元で評価する。
規約：標準単体の元は一般の単体写像を表す。
使われ方：標準形との同値の両方向の計算。
-/
theorem fatDegreeNormalize_inclusion (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (n : ℕ) (x : (F.obj (op ⦋n⦌)).obj d) (t : Δ[n].obj d) :
    fatDegreeNormalize F d ((fatRealizationInclusion F n).app d (x, t)) =
      fatNormalize F d x (SSet.stdSimplex.objEquiv t) :=
  congrArg (fun h => h (⟨n, (x, t)⟩ : (fatRowObject F).obj d)) (fatDegreeNormalize_π F d)

end SerrePositivity.KST.Comparison
