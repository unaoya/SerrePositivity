module

public import SerrePositivity.EInfinity.BarrattEccles.Generators

/-!
# 正規化生成元と単体集合の射の自然性

概要：Berger–Fresse §1.1.2 の正規化鎖の生成元が単体集合の射と可換することを示す。
方針：自由加群化と正規化への射影の自然性を生成元に評価する。
規約：任意の単体集合の射を対象の arity 間で扱う。
使われ方：shuffle 部分合成の等変性と単位の写像を生成元上で検証する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：単体集合の射が誘導する正規化鎖の射（Berger–Fresse §1.1.2）。
方針：自由加群化して正規化 Moore 関手を適用する。
規約：鎖次数は自然数、微分は一つ下がる。
使われ方：単体上の右作用などの構造射を鎖に移す。 -/
def normalizedChainMap {m n : ℕ} (f : simplicial m ⟶ simplicial n) :
    normalizedChains A m ⟶ normalizedChains A n :=
  (AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map ((linearization A).map f)

/-- 概要：線形化した単体集合の射の標準生成元上の値（Berger–Fresse §1.1.2）。
方針：自由加群関手の生成元の像を計算する。
規約：宇宙の持ち上げを自由加群化の前に行う。
使われ方：正規化射影の自然性を生成元へ適用する。 -/
lemma linearization_map_app_freeMk {m n : ℕ} (f : simplicial m ⟶ simplicial n) (q : ℕ)
    (x : (simplicial m) _⦋q⦌) :
    ((linearization A).map f).app _ (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (f.app _ x)) := ModuleCat.free_map_apply _ _

/-- 概要：正規化鎖の射は生成元を像の単体の生成元へ送る（Berger–Fresse §1.1.2）。
方針：正規化 Moore 複体への射影の自然性を標準生成元で評価する。
規約：退化した生成元も含めて成立する。
使われ方：shuffle 和の各項への構造射の作用を計算する。 -/
lemma normalizedChainMap_generator {m n : ℕ} (f : simplicial m ⟶ simplicial n) (q : ℕ)
    (x : (simplicial m) _⦋q⦌) :
    (normalizedChainMap A f).f q (normalizedGenerator A m q x) =
      normalizedGenerator A n q (f.app _ x) := by
  have h := congrArg (fun φ => φ.f q)
    (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_naturality ((linearization A).map f))
  have hv := congrArg (fun φ => φ (ModuleCat.freeMk (ULift.up x))) h
  change (normalizationMap A n).f q
      (((linearization A).map f).app _ (ModuleCat.freeMk (ULift.up x))) =
    (normalizedChainMap A f).f q ((normalizationMap A m).f q (ModuleCat.freeMk (ULift.up x))) at hv
  rw [linearization_map_app_freeMk A f q x] at hv
  exact hv.symm

/-- 概要：整数次数と鎖次数の同型は単体集合の射と可換する（Berger–Fresse §1.1.2）。
方針：次数埋め込みの延長の射の成分公式に逆同型の消去を適用する。
規約：コチェイン次数 −q で自然性を述べる。
使われ方：複体上の作用の等式を正規化鎖へ移す。 -/
lemma complexXIso_naturality {m n : ℕ} (f : simplicial m ⟶ simplicial n) (q : ℕ) :
    ((normalizedFunctor A).map f).f (-(q : ℤ)) ≫ (complexXIso A n q).hom =
      (complexXIso A m q).hom ≫ (normalizedChainMap A f).f q := by
  change (HomologicalComplex.extendMap (normalizedChainMap A f) ComplexShape.embeddingDownNat).f
    (-(q : ℤ)) ≫ (complexXIso A n q).hom = _
  rw [HomologicalComplex.extendMap_f (normalizedChainMap A f) ComplexShape.embeddingDownNat
    (i := q) (i' := -(q : ℤ)) rfl]
  simp only [complexXIso, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：次数同型の逆も単体集合の射と可換する（Berger–Fresse §1.1.2）。
方針：順方向の自然性に逆同型を合成して相殺する。
規約：コチェイン次数 −q で述べる。
使われ方：正規化鎖上の等変性を整数次数の複体の射へ移す。 -/
lemma complexXIso_inv_naturality {m n : ℕ} (f : simplicial m ⟶ simplicial n) (q : ℕ) :
    (complexXIso A m q).inv ≫ ((normalizedFunctor A).map f).f (-(q : ℤ)) =
      (normalizedChainMap A f).f q ≫ (complexXIso A n q).inv := by
  apply (cancel_mono (complexXIso A n q).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [complexXIso_naturality, Iso.inv_hom_id_assoc]

/-- 概要：次数同型の自然性を元に評価する（Berger–Fresse §1.1.2）。
方針：成分の射の自然性を入力の元で評価する。
規約：元の次数は −q である。
使われ方：部分合成の入力への構造射を正規化鎖へ移す。 -/
lemma complexXIso_naturality_apply {m n : ℕ} (f : simplicial m ⟶ simplicial n) (q : ℕ)
    (x : (complex A m).X (-(q : ℤ))) :
    (complexXIso A n q).hom (((normalizedFunctor A).map f).f (-(q : ℤ)) x) =
      (normalizedChainMap A f).f q ((complexXIso A m q).hom x) :=
  congrArg (fun φ => φ x) (complexXIso_naturality A f q)

/-- 概要：逆次数同型の自然性を元に評価する（Berger–Fresse §1.1.2）。
方針：成分の逆自然性を正規化鎖の元で評価する。
規約：鎖次数は q である。
使われ方：部分合成の出力への構造射を正規化鎖へ移す。 -/
lemma complexXIso_inv_naturality_apply {m n : ℕ} (f : simplicial m ⟶ simplicial n) (q : ℕ)
    (x : (normalizedChains A m).X q) :
    ((normalizedFunctor A).map f).f (-(q : ℤ)) ((complexXIso A m q).inv x) =
      (complexXIso A n q).inv ((normalizedChainMap A f).f q x) :=
  congrArg (fun φ => φ x) (complexXIso_inv_naturality A f q)

end SerrePositivity.EInfinity.BarrattEccles
