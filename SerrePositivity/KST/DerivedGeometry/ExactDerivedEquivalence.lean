module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
概要：アーベル圏の加法的同値は実際の Mathlib 導来局所化の同値を与える。
方針：複体の同値と準同型の正確な逆像の一致を局所化する。
規約：導来同値を未証明の仮定として追加しない。
使われ方：Toën §3.2、KST T1′ のアフィン準連接複体の比較。
-/

@[expose] public section
noncomputable section

universe u₁ u₂ v₁ v₂ w₁ w₂
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.IsEquivalence]

/--
概要：加法的同値は複体の準同型を保存かつ反映する。
方針：完全性からコホモロジー比較を使い、同型反映で戻す。
規約：非有界複体の全次数を扱う。
使われ方：Toën §3.2 のアフィン複体局所化。
-/
lemma exactEquivalence_quasiIso_eq :
    HomologicalComplex.quasiIso C (.up ℤ) =
      (HomologicalComplex.quasiIso D (.up ℤ)).inverseImage
        (F.mapHomologicalComplex (.up ℤ)) := by
  ext K L f
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f F).symm

variable [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]

/--
概要：加法的同値による準同型局所化の射は局所化同値。
方針：複体の圏同値と準同型の逆像の一致を使う。
規約：既存の局所化射を使う。
使われ方：Toën §3.2 の通常の圏同値から複体導来圏への移行。
-/
instance exactEquivalence_localizedEquivalence :
    (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)).IsLocalizedEquivalence := by
  let : (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)).functor.IsEquivalence :=
    (F.asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  let : (F.mapHomologicalComplex (.up ℤ)).IsEquivalence :=
    (F.asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  apply LocalizerMorphism.IsLocalizedEquivalence.of_equivalence
  change HomologicalComplex.quasiIso D (.up ℤ) ≤
    (HomologicalComplex.quasiIso C (.up ℤ)).map (F.mapHomologicalComplex (.up ℤ))
  rw [exactEquivalence_quasiIso_eq F, MorphismProperty.map_inverseImage_eq_of_isEquivalence]

/--
概要：Mathlib の完全関手の導来化は元が同値なら同値。
方針：同じ局所化関手に証明済みの局所化同値を適用する。
規約：選択された HasDerivedCategory の導来圏を保持する。
使われ方：Toën §3.2 のアフィン係数複体の導来同値。
-/
instance exactEquivalence_mapDerivedCategory_isEquivalence :
    F.mapDerivedCategory.IsEquivalence := by
  let := exactEquivalence_localizedEquivalence F
  let : CatCommSq (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)).functor
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  exact (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)).isEquivalence
    DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory

/--
概要：アーベル圏の加法的同値が誘導する非有界導来圏の同値。
方針：実際の mapDerivedCategory の同値性を束ねる。
規約：射の像は既存の完全関手の導来化そのもの。
使われ方：Toën §3.2、KST T1′ のアフィン計算。
-/
def exactDerivedEquivalence : DerivedCategory C ≌ DerivedCategory D :=
  F.mapDerivedCategory.asEquivalence

/--
概要：加法的同値から得た導来同値の関手は整数シフトと可換。
方針：Mathlib の完全関手の導来化のシフト比較を保持する。
規約：独立のシフト構造を選び直さない。
使われ方：Toën §3.2 のアフィン導来比較の三角構造。
-/
instance exactDerivedEquivalence_commShift :
    (exactDerivedEquivalence F).functor.CommShift ℤ :=
  inferInstanceAs (F.mapDerivedCategory.CommShift ℤ)

/--
概要：導来同値の逆関手のシフト構造を順関手から構成する。
方針：随伴の単位と余単位に整合する逆シフト比較を使う。
規約：逆関手の構造を独立に選ばない。
使われ方：Toën §3.2 のアフィン導来同値の三角構造。
-/
instance exactDerivedEquivalence_inverseCommShift :
    (exactDerivedEquivalence F).inverse.CommShift ℤ :=
  (exactDerivedEquivalence F).commShiftInverse ℤ

/--
概要：導来同値の単位と余単位はシフトと可換。
方針：順関手から構成した逆シフト比較の整合性を使う。
規約：同じ同値とシフト構造を保持する。
使われ方：Toën §3.2 のアフィン導来同値の三角構造。
-/
instance exactDerivedEquivalence_equivalenceCommShift :
    (exactDerivedEquivalence F).CommShift ℤ :=
  (exactDerivedEquivalence F).commShift_of_functor ℤ

/--
概要：加法的同値が誘導する導来同値は三角同値。
方針：実際の完全関手の導来化が三角関手であることを使う。
規約：Mathlib の標準三角構造を保持する。
使われ方：Toën §3.2、KST T1′ の複体の比較。
-/
instance exactDerivedEquivalence_isTriangulated : (exactDerivedEquivalence F).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _
    (inferInstanceAs F.mapDerivedCategory.IsTriangulated)

end SerrePositivity.KST.DerivedGeometry
