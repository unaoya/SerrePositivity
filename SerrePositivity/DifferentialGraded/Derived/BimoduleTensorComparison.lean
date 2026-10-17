module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorMaps

/-! # 片側の射影的bimodule間の準同型による導来合成関手の比較

## 概要
片側の射影的bimodule間の準同型による導来合成関手の比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
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
variable {Q Q' : BimoduleCategory A C E}

/-- 各右制限が射影的な因子間の準同型は、局所化に値を持つ合成関手の同型を与える。 -/
def composeWithProjectiveIso
    (hQ : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q))
    (hQ' : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q'))
    (g : Q ⟶ Q') (hg : BimoduleCategory.quasiIso A C E g) :
    composeWith A B C E Q ⋙ bimoduleToDerived A B E ≅
      composeWith A B C E Q' ⋙ bimoduleToDerived A B E := by
  let a := whiskerRight (composeWithMap A B C E g) (bimoduleToDerived A B E)
  haveI : ∀ P, IsIso (a.app P) := fun P => bimoduleToDerived_inverts A B E _
    (composeMap_second_projective_quasiIso A B C E P hQ hQ' g hg)
  haveI : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a

@[simp]
lemma composeWithProjectiveIso_hom (hQ hQ' g hg) :
    (composeWithProjectiveIso A B C E (Q := Q) (Q' := Q') hQ hQ' g hg).hom =
      whiskerRight (composeWithMap A B C E g) (bimoduleToDerived A B E) := rfl

/-- 実際の導来圏を始域とする、同じ準同型による合成関手の比較自然同型。 -/
def derivedComposeWithProjectiveIso
    (hF : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hF' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (hQ : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q))
    (hQ' : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q'))
    (g : Q ⟶ Q') (hg : BimoduleCategory.quasiIso A C E g) :
    derivedComposeWith A B C E Q hF ≅ derivedComposeWith A B C E Q' hF' :=
  Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (composeWith A B C E Q ⋙ bimoduleToDerived A B E)
    (composeWith A B C E Q' ⋙ bimoduleToDerived A B E)
    (derivedComposeWith A B C E Q hF) (derivedComposeWith A B C E Q' hF')
    (composeWithProjectiveIso A B C E hQ hQ' g hg)

@[simp]
lemma derivedComposeWithProjectiveIso_hom (hF hF' hQ hQ' g hg) :
    (derivedComposeWithProjectiveIso A B C E (Q := Q) (Q' := Q') hF hF' hQ hQ' g hg).hom =
      derivedComposeWithMap A B C E hF hF' g := rfl

lemma derivedComposeWithProjectiveIso_id
    (hF : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q)) :
    derivedComposeWithProjectiveIso A B C E hF hF hQ hQ (𝟙 Q)
      ((BimoduleCategory.quasiIso A C E).id_mem Q) = Iso.refl _ := by
  apply Iso.ext
  rw [derivedComposeWithProjectiveIso_hom, derivedComposeWithMap_id]
  rfl

lemma derivedComposeWithProjectiveIso_trans {Q'' : BimoduleCategory A C E}
    (hF : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hF' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (hF'' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q''))
    (hQ : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q))
    (hQ' : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q'))
    (hQ'' : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q''))
    (g : Q ⟶ Q') (h : Q' ⟶ Q'')
    (hg : BimoduleCategory.quasiIso A C E g) (hh : BimoduleCategory.quasiIso A C E h) :
    derivedComposeWithProjectiveIso A B C E hF hF' hQ hQ' g hg ≪≫
      derivedComposeWithProjectiveIso A B C E hF' hF'' hQ' hQ'' h hh =
    derivedComposeWithProjectiveIso A B C E hF hF'' hQ hQ'' (g ≫ h)
      ((BimoduleCategory.quasiIso A C E).comp_mem g h hg hh) := by
  apply Iso.ext
  simp only [Iso.trans_hom, derivedComposeWithProjectiveIso_hom]
  exact (derivedComposeWithMap_comp A B C E hF hF' hF'' g h).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
