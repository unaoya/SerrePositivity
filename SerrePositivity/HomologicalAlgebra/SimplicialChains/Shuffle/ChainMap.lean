module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.DifferentialComponents
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.TensorDifferential

/-!
# 一般の正規化 shuffle 鎖写像

概要：Berger–Fresse §1.1.3 の shuffle を正規化鎖のテンソル複体からの射に束ねる。
方針：全次数の余積からの射を構成し、三種類の成分微分公式を適用する。
規約：任意の可換係数環と任意の小さい単体集合を使う。
使われ方：AW 余代数射性と Barratt–Eccles の部分合成との接続。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable (A : Type u) [CommRing A]

/-- 概要：全次数 n の shuffle 射（BF §1.1.3）。
方針：各次数分割の成分を余積の普遍性で束ねる。
規約：出力次数の等式を等式の射で移す。
使われ方：shuffle 鎖写像の各次数の射。 -/
def degreeMap (X Y : SSet.{0}) (n : ℕ) :
    (HomologicalComplex.tensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X)
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y)).X n ⟶ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X n :=
  mapBifunctorDesc (fun p q h => _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y p q ≫
    eqToHom (congrArg (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X h))

/-- 概要：束ねた shuffle 射の包含上の値（BF §1.1.3）。
方針：全テンソル次数の余積の包含公式を用いる。
規約：p+q=n の任意の同定を許す。
使われ方：全複体の微分条件と生成元公式。 -/
@[reassoc (attr := simp)]
lemma ι_degreeMap (X Y : SSet.{0}) (p q n : ℕ) (h : p + q = n) :
    ιTensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y) p q n h ≫
        _root_.SerrePositivity.SimplicialChains.Shuffle.degreeMap A X Y n =
      _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y p q ≫ eqToHom (congrArg (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X h) :=
  ι_mapBifunctorDesc _ _ _ h

/-- 概要：全次数の shuffle 射は微分と可換（BF §1.1.3）。
方針：各次数分割の包含で検査し、正次数・零次数の成分公式を使う。
規約：全微分は n+1 次から n 次へ向かう。
使われ方：一般 shuffle の鎖写像条件。 -/
lemma degreeMap_d (X Y : SSet.{0}) (n : ℕ) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.degreeMap A X Y (n + 1) ≫ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (n + 1) n =
      (HomologicalComplex.tensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y)).d (n + 1) n ≫ _root_.SerrePositivity.SimplicialChains.Shuffle.degreeMap A X Y n := by
  apply mapBifunctor.hom_ext
  intro p q h
  change p + q = n + 1 at h
  cases p with
  | zero =>
    cases q with
    | zero => omega
    | succ q =>
      have hn : n = 0 + q := by omega
      subst n
      rw [_root_.SerrePositivity.SimplicialChains.Shuffle.ι_degreeMap_assoc]
      simp only [eqToHom_refl, Category.id_comp]
      rw [← Category.assoc]
      erw [_root_.SerrePositivity.SimplicialChains.Shuffle.tensorInclusion_d_leftZero (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y) q, Category.assoc, _root_.SerrePositivity.SimplicialChains.Shuffle.ι_degreeMap]
      simp only [eqToHom_refl, Category.comp_id]
      exact _root_.SerrePositivity.SimplicialChains.Shuffle.component_d_leftZero A X Y q
  | succ p =>
    cases q with
    | zero =>
      have hn : n = p + 0 := by omega
      subst n
      rw [_root_.SerrePositivity.SimplicialChains.Shuffle.ι_degreeMap_assoc]
      simp only [eqToHom_refl, Category.id_comp]
      rw [← Category.assoc, _root_.SerrePositivity.SimplicialChains.Shuffle.tensorInclusion_d_rightZero (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y) p, Category.assoc, _root_.SerrePositivity.SimplicialChains.Shuffle.ι_degreeMap]
      simp only [eqToHom_refl, Category.comp_id]
      exact _root_.SerrePositivity.SimplicialChains.Shuffle.component_d_rightZero A X Y p
    | succ q =>
      have hn : n = p + 1 + q := by omega
      subst n
      rw [_root_.SerrePositivity.SimplicialChains.Shuffle.ι_degreeMap_assoc]
      simp only [eqToHom_refl, Category.id_comp]
      rw [← Category.assoc]
      erw [_root_.SerrePositivity.SimplicialChains.Shuffle.tensorInclusion_d_positive (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y) p q, Preadditive.add_comp,
        Preadditive.zsmul_comp]
      simp only [Category.assoc, _root_.SerrePositivity.SimplicialChains.Shuffle.ι_degreeMap, eqToHom_refl, Category.comp_id]
      exact _root_.SerrePositivity.SimplicialChains.Shuffle.component_d_positive A X Y p q

/-- 概要：一般の正規化 shuffle 鎖写像（BF §1.1.3）。
方針：各全次数の余積からの射とその微分可換性を束ねる。
規約：標数・始域の cofibrancy の追加仮定を置かない。
使われ方：AW 余代数射と Barratt–Eccles の Hopf 合成の構成。 -/
def chainMap (X Y : SSet.{0}) :
    HomologicalComplex.tensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y) ⟶
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y) where
  f := _root_.SerrePositivity.SimplicialChains.Shuffle.degreeMap A X Y
  comm' i j h := by
    obtain rfl : i = j + 1 := h.symm
    exact _root_.SerrePositivity.SimplicialChains.Shuffle.degreeMap_d A X Y j

/-- 概要：一般 shuffle 鎖写像の斉次成分は構成済みの shuffle 成分（BF §1.1.3）。
方針：全次数の射の包含上の公式を使う。
規約：出力次数は p+q。
使われ方：生成元公式と余代数射性を鎖写像へ接続する。 -/
@[reassoc (attr := simp)]
lemma ι_chainMap (X Y : SSet.{0}) (p q : ℕ) :
    ιTensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y)
        p q (p + q) rfl ≫ (_root_.SerrePositivity.SimplicialChains.Shuffle.chainMap A X Y).f (p + q) = _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y p q := by
  simpa only [_root_.SerrePositivity.SimplicialChains.Shuffle.chainMap, eqToHom_refl, Category.comp_id] using _root_.SerrePositivity.SimplicialChains.Shuffle.ι_degreeMap A X Y p q (p + q) rfl

end SerrePositivity.SimplicialChains.Shuffle
