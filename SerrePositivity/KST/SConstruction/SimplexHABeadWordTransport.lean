module
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordCells
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.SimplexHABeadTail

/-! # 元の bead 語の次元移送と評価
概要：bead 語の次元移送を、元の dg Hom 成分の同じ次数移送として回収する。
方針：次元等号と端点等号を消去し、元の部分集合成分の定義に戻す。
規約：元の語と元の HA 成分を保持。使われ方：読み替えの計算式から移送を外す。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の語の逆向き次元移送は、値の同じ逆向き次数移送を回収する。 -/
lemma simplexHABeadWordValue_mpr {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {a b : Fin (n + 1)} {p q : ℕ} (h : p = q) (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b q) :
    simplexHABeadWordValue A s (Eq.mpr (congrArg (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b) h) word) =
      eqToHom (congrArg (fun k => (homObject A D (s.obj a) (s.obj b)).X k)
        (congrArg (fun d : ℕ => -(d : ℤ)) h.symm)) (simplexHABeadWordValue A s word) := by
  cases h
  rfl

/-- 元の端点を指定した一 bead の語の評価は、同じ指定端点・次数の HA 成分。 -/
lemma simplexHABeadWordAt_value {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (a b : Fin (n + 1))
    (ha : a = I.min' (Finset.card_pos.mp (by omega)))
    (hb : b = I.max' (Finset.card_pos.mp (by omega))) :
    simplexHABeadWordValue A s (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordAt I hI a b ha hb) =
      s.hom I a b (-((I.card - 2 : ℕ) : ℤ)) hI ha hb (by omega) := by
  subst a b
  rfl

/-- 同じ HA 成分の指定次数を変えると、同じ dg Hom 加群の次数移送を回収する。 -/
lemma simplexHAComponent_degree_transport {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (a b : Fin (n + 1))
    (ha : a = I.min' (Finset.card_pos.mp (by omega)))
    (hb : b = I.max' (Finset.card_pos.mp (by omega)))
    (p q : ℤ) (hp : p = 2 - (I.card : ℤ)) (hq : q = 2 - (I.card : ℤ)) (h : p = q) :
    eqToHom (congrArg (fun k => (homObject A D (s.obj a) (s.obj b)).X k) h)
        (s.hom I a b p hI ha hb hp) = s.hom I a b q hI ha hb hq := by
  cases h
  rfl

end SerrePositivity.KST.SConstruction
