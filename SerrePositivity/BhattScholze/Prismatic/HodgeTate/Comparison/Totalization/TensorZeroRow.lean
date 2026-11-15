module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TensorComponents

/-!
# テンソル–積全複体の比較と零行の射影

## 概要
次数ごとの標準比較射が、零行の指定射影と可換であることを示す。

## 方針
零行の射影を鎖写像として構成し、テンソルの同次成分で標準比較と照合する。

## 規約
零行への射影に任意の選択を使わない。正の横次数の比較は別の法則で扱う。

## 使われ方
BS 著者版 Lemma 4.22 の標準比較射の鎖写像性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.HomologicalAlgebra.CochainProductTotal
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R : Type u} [CommRing R]

private theorem degree_transport (C : Complex R) (i j i' j' : ℤ)
    (hi : i = i') (hj : j = j') :
    eqToHom (congrArg C.X hi) ≫ C.d i' j' = C.d i j ≫ eqToHom (congrArg C.X hj) := by
  subst i'
  subst j'
  simp

private theorem map_degree_transport {C D : Complex R} (g : C ⟶ D) (i j : ℤ)
    (h : i = j) :
    eqToHom (congrArg C.X h) ≫ g.f j = g.f i ≫ eqToHom (congrArg D.X h) := by
  subst j
  simp

@[reassoc] private theorem tensor_ι_transport (L Q : Complex R)
    (a b q b' q' : ℤ) (hab : a + b = q) (hb : b = b') (hq : q = q') :
    (L.X a ◁ eqToHom (congrArg Q.X hb)) ≫ ιTensorObj L Q a b' q' (by omega) =
      ιTensorObj L Q a b q hab ≫ eqToHom (congrArg (cochainTensor L Q).X hq) := by
  subst b'
  subst q'
  simp

/-- 積全複体から元の零行への、指定成分による鎖写像。 -/
def zeroRowHom (K : CochainComplex (Complex R) ℕ) : total K ⟶ K.X 0 where
  f q := componentπ K 0 q ≫ eqToHom
    (congrArg (K.X 0).X (by omega : q - ((0 : ℕ) : ℤ) = q))
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst j
    rw [Category.assoc, degree_transport (K.X 0) (i - ((0 : ℕ) : ℤ))
      (i + 1 - ((0 : ℕ) : ℤ)) i (i + 1) (by omega) (by omega)]
    erw [← Category.assoc, ← component_d_zero K i]
    simp only [Category.assoc]

/-- 零行への射影は二重複体の鎖写像に関して自然である。 -/
@[reassoc] theorem zeroRowHom_naturality {K M : CochainComplex (Complex R) ℕ}
    (g : K ⟶ M) :
    ((SerrePositivity.HomologicalAlgebra.cochainProductTotalizationFunctor
      (ModuleCat.{u} R)).map g) ≫ zeroRowHom M = zeroRowHom K ≫ g.f 0 := by
  ext q
  dsimp only [zeroRowHom, HomologicalComplex.comp_f]
  rw [Category.assoc, map_degree_transport (g.f 0) (q - ((0 : ℕ) : ℤ)) q (by omega)]
  rw [← Category.assoc, ← Category.assoc, componentπ_naturality]

/-- 標準比較の零行成分は、元の零行射影をテンソルしたものそのものである。 -/
@[reassoc] theorem tensorComparisonDegree_zeroRow (L : Complex R)
    (K : CochainComplex (Complex R) ℕ) (q : ℤ) :
    tensorComparisonDegree L K q ≫ (zeroRowHom (tensorRows L K)).f q =
      (cochainTensorMap (𝟙 L) (zeroRowHom K)).f q := by
  apply mapBifunctor.hom_ext
  intro a b hab
  dsimp only [zeroRowHom]
  rw [tensorComparisonDegree_component_assoc, ιTensorObj_cochainTensorMap]
  simp only [tensorComponent, interchangeSign, Int.natCast_zero, mul_zero,
    Int.negOnePow_zero, one_smul, tensorHom_def, HomologicalComplex.id_f,
    id_whiskerRight, Category.id_comp, whiskerLeft_comp, Category.assoc]
  rw [tensor_ι_transport] <;> simp

/-- 零行成分では、標準比較は全微分と可換である。 -/
theorem tensorComparisonDegree_comm_zeroRow (L : Complex R)
    (K : CochainComplex (Complex R) ℕ) (q : ℤ) :
    tensorComparisonDegree L K q ≫ (total (tensorRows L K)).d q (q + 1) ≫
        (zeroRowHom (tensorRows L K)).f (q + 1) =
      (cochainTensor L (total K)).d q (q + 1) ≫ tensorComparisonDegree L K (q + 1) ≫
        (zeroRowHom (tensorRows L K)).f (q + 1) := by
  rw [← (zeroRowHom (tensorRows L K)).comm]
  rw [← Category.assoc, tensorComparisonDegree_zeroRow, tensorComparisonDegree_zeroRow]
  exact (cochainTensorMap (𝟙 L) (zeroRowHom K)).comm q (q + 1)

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
