module

public import SerrePositivity.KST.Comparison.FatRealization
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexImageMono

/-!
# fat realization の各次数の全射な標準形

概要：行と標準単体の組を全射な単体写像と行の元の組へ正規化する。
方針：単体写像の epi–mono 分解の単射側を行へ作用させる。
規約：Segal 1974 Proposition 1.6、Appendix A の fat realization の計算。
使われ方：面の関係式で不変な標準形を、実際の余等化子へ降ろす。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite

/--
概要：fat realization の固定した次数の全射な標準形のデータ。
方針：終域の単体、全射、対応する行の単体を記録する。
規約：全射性は既存の Epi 条件で表す。
使われ方：各次数の余等化子の具体的な元の表示。
-/
structure FatNormalForm (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ) where
  degree : SimplexCategory
  epi : d.unop ⟶ degree
  epi_property : Epi epi
  simplex : (F.obj (op degree)).obj d

/--
概要：任意の行の元と単体写像を全射な標準形へ送る。
方針：像への全射を添字とし、像の包含を行へ反変に作用させる。
規約：像の対象は Mathlib の epi–mono 分解の選択そのもの。
使われ方：余等化子の関係式に対して不変な写像。
-/
def fatNormalize (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ)
    {n : SimplexCategory} (x : (F.obj (op n)).obj d) (t : d.unop ⟶ n) : FatNormalForm F d where
  degree := image t
  epi := factorThruImage t
  epi_property := inferInstance
  simplex := (F.map (image.ι t).op).app d x

/--
概要：正規化は指定した任意の epi–mono 分解でも計算できる。
方針：単体圏が骨格圏であることによる像の対象と二因子の一意性を使う。
規約：指定した中間対象へ輸送する部分は対象の等式で処理する。
使われ方：面との合成と全射そのものの場合の計算。
-/
theorem fatNormalize_eq_of_factorization (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) {n k : SimplexCategory} (x : (F.obj (op n)).obj d)
    (t : d.unop ⟶ n) (e : d.unop ⟶ k) [Epi e] (j : k ⟶ n) [Mono j] (h : e ≫ j = t) :
    fatNormalize F d x t = ⟨k, e, inferInstance, (F.map j.op).app d x⟩ := by
  have hk := SimplexCategory.image_eq h
  subst k
  have hj := SimplexCategory.image_ι_eq h
  have he := SimplexCategory.factorThruImage_eq h
  simp only [fatNormalize, hj, he]

/--
概要：面の二つの関係式は正規化で同じ全射な標準形に入る。
方針：元の像分解に面の単射を後合成し、関手の合成則を使う。
規約：面は任意の単射であり、標準の余面に限らない。
使われ方：正規化を fat realization の余等化子へ降ろす条件。
-/
theorem fatNormalize_face (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ)
    {n n' : SimplexCategory} (θ : n ⟶ n') [Mono θ]
    (x : (F.obj (op n')).obj d) (t : d.unop ⟶ n) :
    fatNormalize F d ((F.map θ.op).app d x) t = fatNormalize F d x (t ≫ θ) := by
  have hfac : factorThruImage t ≫ (image.ι t ≫ θ) = t ≫ θ := by
    rw [← Category.assoc, image.fac]
  rw [fatNormalize_eq_of_factorization F d x (t ≫ θ) (factorThruImage t) (image.ι t ≫ θ) hfac]
  unfold fatNormalize
  rw [op_comp, F.map_comp]
  rfl

/--
概要：既に全射である標準形を正規化しても変わらない。
方針：全射と終域の恒等射の分解を使う。
規約：Epi の証明の選択は証明の無関連性で消える。
使われ方：各次数の標準形から余等化子への逆写像の復元。
-/
theorem fatNormalize_of_normalForm (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (p : FatNormalForm F d) :
    fatNormalize F d p.simplex p.epi = p := by
  rcases p with ⟨k, e, he, x⟩
  let : Epi e := he
  rw [fatNormalize_eq_of_factorization F d x e e (𝟙 k) (Category.comp_id _)]
  rw [op_id, F.map_id]
  rfl

end SerrePositivity.KST.Comparison
