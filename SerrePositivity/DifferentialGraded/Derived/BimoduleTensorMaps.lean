module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensor

/-! # 固定因子の射による合成関手とその局所化の自然変換

## 概要
固定因子の射による合成関手とその局所化の自然変換。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleTensorAssociator.lean、Derived/
BimoduleTensorFunctor.lean、Derived/BimoduleTensorKFlatComparison.lean等。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

def composeWithMap {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q') :
    composeWith A B C E Q ⟶ composeWith A B C E Q' where
  app P := composeMap A B C E (𝟙 P) g
  naturality {P P'} f := by
    have h₁ := composeMap_comp A B C E f (𝟙 P') (𝟙 Q) g
    have h₂ := composeMap_comp A B C E (𝟙 P) f g (𝟙 Q')
    simp only [Category.comp_id, Category.id_comp] at h₁ h₂
    exact h₁.symm.trans h₂

lemma composeWithMap_id (Q : BimoduleCategory A C E) :
    composeWithMap A B C E (𝟙 Q) = 𝟙 (composeWith A B C E Q) := by
  apply NatTrans.ext
  funext P
  exact composeMap_id A B C E P Q

lemma composeWithMap_comp {Q Q' Q'' : BimoduleCategory A C E} (g : Q ⟶ Q') (h : Q' ⟶ Q'') :
    composeWithMap A B C E (g ≫ h) = composeWithMap A B C E g ≫ composeWithMap A B C E h := by
  apply NatTrans.ext
  funext P
  change composeMap A B C E (𝟙 P) (g ≫ h) =
    composeMap A B C E (𝟙 P) g ≫ composeMap A B C E (𝟙 P) h
  have hh := composeMap_comp A B C E (𝟙 P) (𝟙 P) g h
  simpa only [Category.id_comp] using hh

/-- Qの射を、局所化の自然変換の普遍性によって降ろす。 -/
def derivedComposeWithMap {Q Q' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (g : Q ⟶ Q') : derivedComposeWith A B C E Q hQ ⟶ derivedComposeWith A B C E Q' hQ' :=
  Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (composeWith A B C E Q ⋙ bimoduleToDerived A B E)
    (composeWith A B C E Q' ⋙ bimoduleToDerived A B E)
    (derivedComposeWith A B C E Q hQ) (derivedComposeWith A B C E Q' hQ')
    (whiskerRight (composeWithMap A B C E g) (bimoduleToDerived A B E))

lemma derivedComposeWithMap_app {Q Q' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (g : Q ⟶ Q') (P : BimoduleCategory A B C) :
    (derivedComposeWithMap A B C E hQ hQ' g).app ((bimoduleToDerived A B C).obj P) =
      (derivedComposeWithComputation A B C E Q hQ P).hom ≫
        (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) g) ≫
          (derivedComposeWithComputation A B C E Q' hQ' P).inv :=
  Localization.liftNatTrans_app (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (composeWith A B C E Q ⋙ bimoduleToDerived A B E)
    (composeWith A B C E Q' ⋙ bimoduleToDerived A B E)
    (derivedComposeWith A B C E Q hQ) (derivedComposeWith A B C E Q' hQ')
    (whiskerRight (composeWithMap A B C E g) (bimoduleToDerived A B E)) P

lemma derivedComposeWithMap_id (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    derivedComposeWithMap A B C E hQ hQ (𝟙 Q) = 𝟙 (derivedComposeWith A B C E Q hQ) := by
  unfold derivedComposeWithMap
  rw [composeWithMap_id]
  have hid : whiskerRight (𝟙 (composeWith A B C E Q)) (bimoduleToDerived A B E) =
      𝟙 (composeWith A B C E Q ⋙ bimoduleToDerived A B E) := by
    apply NatTrans.ext
    funext P
    exact (bimoduleToDerived A B E).map_id ((composeWith A B C E Q).obj P)
  rw [hid]
  exact Localization.liftNatTrans_id _ _ _ _

lemma derivedComposeWithMap_comp {Q Q' Q'' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (hQ'' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q''))
    (g : Q ⟶ Q') (h : Q' ⟶ Q'') :
    derivedComposeWithMap A B C E hQ hQ'' (g ≫ h) =
      derivedComposeWithMap A B C E hQ hQ' g ≫ derivedComposeWithMap A B C E hQ' hQ'' h := by
  unfold derivedComposeWithMap
  rw [Localization.comp_liftNatTrans, composeWithMap_comp, whiskerRight_comp]

end SerrePositivity.DifferentialGraded.BimoduleTensor
