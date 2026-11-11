module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Eilenberg–Zilber の shuffle の成分写像

概要：二つの因子の退化写像のテンソルを格子路の符号付き有限和として構成する。
方針：二重次数 p,q ごとの和を全テンソルの余積の降下写像で束ねる。
規約：KST Construction A.5 の標準 shuffle、次数 p+q=n。
使われ方：正規化 AW の逆方向の比較。成分構成だけで鎖写像性や標準ホモトピーの完成とはしない。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology
open scoped Simplicial

/-- 概要：二重次数 p,q の shuffle の実成分写像。
方針：全ての格子路の退化写像のテンソルを逆転数の符号で足す。
規約：KST A.5、全次数 p+q=n。
使われ方：全テンソルの各直和成分からの写像。 -/
@[kerodon 00RJ]
def shuffleBidegree (C D : SimplicialObject (ModuleCat.{u} ℤ))
    (p q n : ℕ) (h : p + q = n) :
    integerTensor (C.obj (op ⦋p⦌)) (D.obj (op ⦋q⦌)) ⟶
      (simplicialIntegerTensor C D).obj (op ⦋n⦌) :=
  ∑ s : ShuffleIndex p n, (-1 : ℤ) ^ s.inversions •
    integerTensorMap (C.map s.left.op) (D.map (s.right h).op)

/-- 概要：全テンソルの全次数 n から次数ごとの単体的テンソルへの shuffle の写像。
方針：各二重次数の写像を全複体の余積から降下させる。
規約：KST Construction A.5、任意の加群の宇宙。
使われ方：鎖写像性と AW との標準比較に使う実成分。 -/
@[kerodon 00RJ]
def shuffleApp (C D : SimplicialObject (ModuleCat.{u} ℤ)) (n : ℕ) :
    (chainIntegerTensor ((alternatingFaceMapComplex _).obj C)
      ((alternatingFaceMapComplex _).obj D)).X n ⟶
      (simplicialIntegerTensor C D).obj (op ⦋n⦌) :=
  mapBifunctorDesc (fun p q h ↦ shuffleBidegree C D p q n h)

/-- 概要：shuffle の全次数の写像を標準直和成分へ制限すると二重次数の和になる。
方針：全複体の余積からの降下写像の評価公式を使う。
規約：KST A.5。使われ方：鎖写像性を各二重次数で確認する。 -/
@[reassoc (attr := simp)] lemma ι_shuffleApp
    (C D : SimplicialObject (ModuleCat.{u} ℤ)) (p q n : ℕ)
    (h : ComplexShape.π (.down ℕ) (.down ℕ) (.down ℕ) (p, q) = n) :
    ιMapBifunctor ((alternatingFaceMapComplex _).obj C)
      ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) p q n h ≫
      shuffleApp C D n = shuffleBidegree C D p q n h :=
  ι_mapBifunctorDesc _ _ _ _

/-- 概要：shuffle の二重次数の成分は二つの単体的整数加群の射に自然。
方針：各格子路で二つの退化写像との自然性をテンソルし、有限和を取る。
規約：KST A.5、外部作用も含む。
使われ方：shuffle の自然性と同変性。 -/
lemma shuffleBidegree_naturality
    {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D')
    (p q n : ℕ) (h : p + q = n) :
    integerTensorMap (f.app (op ⦋p⦌)) (g.app (op ⦋q⦌)) ≫ shuffleBidegree C' D' p q n h =
      shuffleBidegree C D p q n h ≫ integerTensorMap (f.app (op ⦋n⦌)) (g.app (op ⦋n⦌)) := by
  simp only [shuffleBidegree, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  rw [← integerTensorMap_comp, ← integerTensorMap_comp]
  exact congrArg₂ integerTensorMap (f.naturality s.left.op).symm (g.naturality (s.right h).op).symm

/-- 概要：shuffle の全次数の成分は二つの入力の射に自然。
方針：全テンソルの標準包含ごとに二重次数の自然性を適用する。
規約：KST A.5。使われ方：比較の外部 G 同変性と正規化への移送。 -/
lemma shuffleApp_naturality
    {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D') (n : ℕ) :
    (chainIntegerTensorMap ((alternatingFaceMapComplex _).map f)
      ((alternatingFaceMapComplex _).map g)).f n ≫ shuffleApp C' D' n =
    shuffleApp C D n ≫ integerTensorMap (f.app (op ⦋n⦌)) (g.app (op ⦋n⦌)) := by
  apply mapBifunctor.hom_ext
  intro p q h
  rw [← Category.assoc, ι_chainIntegerTensorMap, Category.assoc, ι_shuffleApp,
    ← Category.assoc, ι_shuffleApp]
  exact shuffleBidegree_naturality f g p q n h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
