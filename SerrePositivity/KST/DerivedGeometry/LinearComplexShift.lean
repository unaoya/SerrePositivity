module

public import SerrePositivity.KST.DerivedGeometry.LinearComplexEnrichment
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# 一般の線形加法圏の写像複体の右 shift

概要：Hom(X,Y) の shift と Hom(X,Y[s]) の具体的な chain 同型を構成する。
方針：Mathlib の cochain の右 shift の線形同値と微分公式を使う。
規約：shift の微分の符号を維持し、次数別の全単射だけで済ませない。
使われ方：KST D4・§10-7、Drinfeld §2.4、Toën Derived Azumaya §3.2 の前三角化比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.KST.DerivedGeometry.LinearComplex

variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]

/--
概要：写像複体の shift から、標的を shift した写像複体への射。
方針：右 shift の線形同値を各次数へ置き、δ_rightShift で微分との可換性を示す。
規約：元の複体の shift と写像複体の shift に同じ整数を使う。
使われ方：Drinfeld §2.4、KST D4 の代表加群の shift の表示。
-/
def mappingShiftMap (X Y : CochainComplex C ℤ) (s : ℤ) :
    (mappingComplex A X Y)⟦s⟧ ⟶ mappingComplex A X (Y⟦s⟧) :=
  CochainComplex.ofHom
    (fun q => ModuleCat.ofHom (Cochain.rightShiftLinearEquiv A X Y (q + s) s q rfl).toLinearMap)
    (fun q => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change δ q (q + 1) (f.rightShift s q rfl) =
        (s.negOnePow • δ (q + s) (q + 1 + s) f).rightShift s (q + 1) rfl
      rw [Cochain.δ_rightShift f s q (q + 1) rfl (q + 1 + s) rfl,
        Cochain.rightShift_units_smul])

/--
概要：右 shift 比較射は各次数で全単射。
方針：cochain の右 shift の線形同値を使う。
規約：複体の射としての構成を先に済ませている。
使われ方：Drinfeld §2.4、KST D4 の具体的な chain 同型。
-/
instance mappingShiftMap_isIso (X Y : CochainComplex C ℤ) (s : ℤ) :
    IsIso (mappingShiftMap A X Y s) := by
  have (q : ℤ) : IsIso ((mappingShiftMap A X Y s).f q) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (Cochain.rightShiftLinearEquiv A X Y (q + s) s q rfl).bijective
  exact HomologicalComplex.Hom.isIso_of_components _

/--
概要：写像複体の shift と、標的の shift の写像複体との同型。
方針：具体的な微分可換の右 shift 比較射を同型へ束ねる。
規約：有界性・平坦性は要求しない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の前三角化の代表可能性。
-/
def mappingShiftIso (X Y : CochainComplex C ℤ) (s : ℤ) :
    (mappingComplex A X Y)⟦s⟧ ≅ mappingComplex A X (Y⟦s⟧) :=
  asIso (mappingShiftMap A X Y s)

/--
概要：標的の右 shift は、任意次数の前合成と両立する。
方針：右 shift の逆写像で比較し、Mathlib の rightUnshift_comp を使う。
規約：次数零の射だけでなく全次数の cochain を扱う。
使われ方：Drinfeld §2.4、KST D4 の代表 dg 加群の shift 自然性。
-/
theorem rightShift_comp {X Y Z : CochainComplex C ℤ} {p r m q n s : ℤ}
    (f : Cochain X Y p) (g : Cochain Y Z r)
    (hm : p + r = m) (hn : n + s = m) (hq : q + s = r) :
    (f.comp g hm).rightShift s n hn =
      f.comp (g.rightShift s q hq) (by omega) := by
  apply (Cochain.rightShiftAddEquiv X Z m s n hn).symm.injective
  change ((f.comp g hm).rightShift s n hn).rightUnshift m hn =
    (f.comp (g.rightShift s q hq) _).rightUnshift m hn
  rw [Cochain.rightUnshift_rightShift,
    Cochain.rightUnshift_comp f (g.rightShift s q hq) (by omega) m hn r hq,
    Cochain.rightUnshift_rightShift]

end SerrePositivity.KST.DerivedGeometry.LinearComplex
