module

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.EInfinity.Interface.PrimeFieldMap

/-!
# 素体の P⁰ を係数の制限で読む

May, Proposition 2.3・BS 著者版 Lemma 8.4 の補助。
一般の標数 p の環での演算は、素体の本欄をホモロジーの自然同型で共役する。
模型の API と coherent な Sp 値の持ち上げは使わない。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory SSet

/-- 係数の制限は、台の全整数次数のホモトピー可換群を自然に保つ。 -/
def EInfinityTheory.restrictHomotopyGroupsIso (E : EInfinityTheory.{u})
    {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) (n : ℤ) :
    hoMap (E.restrict f) ⋙ homotopyGroupsOnHo S (E.forget S) n ≅
      homotopyGroupsOnHo T (E.forget T) n := by
  let compIso {X Y Z : SSet.{u + 1}} (a : X ⟶ Y) (b : Y ⟶ Z) :
      hoMap (a ≫ b) ≅ hoMap a ⋙ hoMap b := by
    apply eqToIso
    change (hoFunctor.map (a ≫ b)).toFunctor = _
    rw [hoFunctor.map_comp]
    rfl
  let e : hoMap (E.restrict f) ⋙ hoMap (E.forget S) ≅
      hoMap (E.forget T) ⋙ hoMap (E.restrictD f) :=
    (compIso (E.restrict f) (E.forget S)).symm ≪≫
      (E.restrict_forget f).toNatIso ≪≫
        compIso (E.forget T) (E.restrictD f)
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e (additiveCohomologyOnHo S (-n)) ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (hoMap (E.forget T)) (E.restrictD_homologyIso f (-n))

/-- 一般 k では素体へ制限し、指定の自然同型で共役して同じ P⁰ を読む。 -/
def EInfinityTheory.powerOp0Over (E : EInfinityTheory.{u}) (k : Type u) [CommRing k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℤ) :
    homotopyGroupsOnHo k (E.forget k) n ⟶ homotopyGroupsOnHo k (E.forget k) n := by
  let f := eInfinityPrimeFieldMap p k
  let e := E.restrictHomotopyGroupsIso f n
  exact e.inv ≫ Functor.whiskerLeft (hoMap (E.restrict f)) (E.powerOp0 p n) ≫ e.hom

end SerrePositivity.EInfinity
