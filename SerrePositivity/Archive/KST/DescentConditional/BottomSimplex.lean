module

public import SerrePositivity.Archive.KST.DescentConditional.CechAdjointReindex
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.WideSubcategory
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Order.Fin.Tuple
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# 最小元を保つ単体添字と自由な最小元の付加

## 概要
最小元を保つ有限非空順序の圏を構成し、自由な最小元を付加する関手の随伴を証明する。

## 方針
単体圏の最小元を保つ射による広い部分圏を使い、有限順序写像の頭と尾を分ける。

## 規約
付加する最小元は元の最小元とは別。忘却関手との随伴は実際の Hom 同値から構成する。

## 使われ方
論文 補題 3.2 の分裂余単体対象の添字変更。τ 位相の層論を Čech 計算で置換する準備。
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.KST.Descent

/-- 概要：最小元を保つ単体射（補題 3.2 の分裂添字）。
方針：順序写像の零での値を検査する。規約：始域・終域とも非空。
使われ方：分裂余単体対象の添字の広い部分圏。 -/
def preservesSimplexBottom : MorphismProperty SimplexCategory :=
  fun _ _ f ↦ f.toOrderHom 0 = 0

instance : preservesSimplexBottom.IsMultiplicative where
  id_mem _ := rfl
  comp_mem f g hf hg := by
    change g.toOrderHom (f.toOrderHom 0) = 0
    rw [hf, hg]

/-- 概要：最小元を保つ有限非空順序の実際の圏（補題 3.2）。
方針：単体圏の広い部分圏を使う。規約：零番目の点を区別する。
使われ方：extra degeneracy を保持する添字。 -/
abbrev BottomSimplex := WideSubcategory preservesSimplexBottom

namespace BottomSimplex

/-- 概要：区別した最小元を忘れる実際の関手（補題 3.2）。
方針：広い部分圏の包含。規約：元の有限順序全体を保つ。
使われ方：自由な最小元の付加の右随伴。 -/
abbrev forget : BottomSimplex ⥤ SimplexCategory :=
  wideSubcategoryInclusion preservesSimplexBottom

/-- 概要：順序写像に最小元を付加（補題 3.2）。
方針：零には零、後続元には元の像の後続元を対応させる。
規約：既存の元は一つずつ移す。使われ方：自由な最小元の付加関手の射。 -/
def adjoinMap {n m : SimplexCategory} (f : n ⟶ m) :
    (⟨⦋n.len + 1⦌⟩ : BottomSimplex) ⟶ ⟨⦋m.len + 1⦌⟩ :=
  ⟨SimplexCategory.Hom.mk
    ⟨Fin.cons 0 (fun i ↦ (f.toOrderHom i).succ),
      (monotone_vecCons).2
        ⟨Fin.zero_le _, fun _ _ h ↦ Fin.succ_le_succ_iff.mpr (f.toOrderHom.monotone h)⟩⟩,
    rfl⟩

/-- 概要：自由な最小元を付加する実際の関手（補題 3.2）。
方針：各順序の先頭に新しい元を置き、全射を頭と尾で検査する。
規約：元の最小元も後続元へ移す。使われ方：分裂余単体対象の添字変更。 -/
def adjoin : SimplexCategory ⥤ BottomSimplex where
  obj n := ⟨⦋n.len + 1⦌⟩
  map f := adjoinMap f
  map_id n := by
    apply WideSubcategory.hom_ext
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
  map_comp f g := by
    apply WideSubcategory.hom_ext
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl

/-- 概要：最小元を付加した始域の射と元の順序写像の実際の同値（補題 3.2）。
方針：順序写像の尾を取り、逆に零を頭へ付加する。
規約：尾の値は零でもよい。使われ方：添字随伴の Hom 対応。 -/
def homEquiv (n : SimplexCategory) (m : BottomSimplex) :
    (adjoin.obj n ⟶ m) ≃ (n ⟶ forget.obj m) where
  toFun f := SimplexCategory.Hom.mk
    ⟨fun i ↦ f.hom.toOrderHom i.succ,
      fun _ _ h ↦ f.hom.toOrderHom.monotone (Fin.succ_le_succ_iff.mpr h)⟩
  invFun f :=
    ⟨SimplexCategory.Hom.mk
      ⟨Fin.cons 0 f.toOrderHom,
        (monotone_vecCons).2 ⟨Fin.zero_le _, f.toOrderHom.monotone⟩⟩,
      rfl⟩
  left_inv f := by
    apply WideSubcategory.hom_ext
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact congrArg Fin.val f.property.symm
    · rfl
  right_inv f := by ext i; rfl

/-- 概要：最小元の自由な付加は忘却の左随伴（補題 3.2）。
方針：実際の尾の Hom 同値の両側自然性を各元で検査する。
規約：添字変更の余終性を公理にしない。使われ方：実際のホモトピー極限の添字変更。 -/
def adjunction : adjoin ⊣ forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := by
        intro n' n m f g
        apply WideSubcategory.hom_ext
        ext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
      homEquiv_naturality_right := by
        intro n m m' f g
        ext i
        rfl }

/-- 概要：一点順序は最小元を保つ添字圏の始対象（補題 3.2）。
方針：始域の唯一の点は最小元へ写ることを各射の条件から導く。
規約：単体圏全体の始対象とは主張しない。使われ方：分裂側の増強の値の計算。 -/
def initial : CategoryTheory.Limits.IsInitial (⟨⦋0⦌⟩ : BottomSimplex) :=
  CategoryTheory.Limits.IsInitial.ofUniqueHom
    (fun m ↦ ⟨SimplexCategory.const _ m.obj 0, rfl⟩)
    (fun m f ↦ by
      apply WideSubcategory.hom_ext
      apply SimplexCategory.Hom.ext_zero_left
      exact f.property)

section HomotopyLimit

open CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

variable [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：最小元を付加する添字への制限は実際のホモトピー極限を保つ（補題 3.2）。
方針：構成済みの実際の添字随伴に、局所化後のホモトピー極限の添字変更を適用する。
規約：同型は局所化後。指定増強との整合性は別工程。使われ方：分裂余単体対象への接続。 -/
def homotopyLimitRestrictionIso {H : Type*} [Category* H]
    (Λ : SSet.{0} ⥤ H) [Λ.IsLocalization (weakEquivalences SSet.{0})]
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _) :
    HomotopyCones.functor BottomSimplex I J ⋙ Λ ≅
      CechReindex.precomp adjoin ⋙ HomotopyCones.functor SimplexCategory I J ⋙ Λ :=
  CechReindex.homotopyLimitCanonicalIso SimplexCategory I J Λ BottomSimplex adjunction hcof

end HomotopyLimit

end BottomSimplex
end SerrePositivity.KST.Descent
