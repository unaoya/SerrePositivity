module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorMaps
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon

/-! # 固定した右相対K-flat二因子に関する導来合成の結合比較

## 概要
固定した右相対K-flat二因子に関する導来合成の結合比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleTensorEvaluation.lean。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)

/-- 元の閉零合成関手の、前のbimodule変数に自然な結合比較。 -/
def composeWithAssociatorIso :
    composeWith A B C E Q ⋙ composeWith A B E F R ≅ composeWith A B C F (BimoduleCategory.of A C F
      (compose A C E F
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R))) :=
  NatIso.ofComponents
    (fun P => associatorIso A B C E F (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R))
    (fun f => by
      have h := associatorIso_naturality A B C E F f (𝟙 Q) (𝟙 R)
      rw [composeMap_id] at h
      exact h)

@[simp]
lemma composeWithAssociatorIso_app (P : BimoduleCategory A B C) :
    (composeWithAssociatorIso A B C E F Q R).app P =
      associatorIso A B C E F (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A
      C E Q) (BimoduleCategory.underlying A E F R) := rfl

variable (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
  (hR : Bimodule.rightRelativeKFlat A E F (BimoduleCategory.underlying A E F R))
include hQ hR

lemma derivedComposeWithPair_fac :
    bimoduleToDerived A B C ⋙
        (derivedComposeWith A B C E Q hQ ⋙ derivedComposeWith A B E F R hR) =
      (composeWith A B C E Q ⋙ composeWith A B E F R) ⋙ bimoduleToDerived A B F := by
  rfl

instance derivedComposeWithPair_lifting :
    Localization.Lifting (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      ((composeWith A B C E Q ⋙ composeWith A B E F R) ⋙ bimoduleToDerived A B F)
      (derivedComposeWith A B C E Q hQ ⋙ derivedComposeWith A B E F R hR) :=
  ⟨eqToIso (derivedComposeWithPair_fac A B C E F Q R hQ hR)⟩

/-- 右相対K-flat性の合成閉性を使った、実際の導来圏上の結合自然同型。 -/
def derivedAssociatorIso :
    derivedComposeWith A B C E Q hQ ⋙ derivedComposeWith A B E F R hR ≅
      derivedComposeWith A B C F (BimoduleCategory.of A C F (compose A C E F
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)))
      (Bimodule.rightRelativeKFlat_compose A C E F (BimoduleCategory.underlying A C E Q)
      (BimoduleCategory.underlying A E F R) hQ hR) :=
  Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    ((composeWith A B C E Q ⋙ composeWith A B E F R) ⋙ bimoduleToDerived A B F)
    (composeWith A B C F (BimoduleCategory.of A C F (compose A C E F
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R))) ⋙
      bimoduleToDerived A B F)
    (derivedComposeWith A B C E Q hQ ⋙ derivedComposeWith A B E F R hR)
    (derivedComposeWith A B C F (BimoduleCategory.of A C F (compose A C E F
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)))
      (Bimodule.rightRelativeKFlat_compose A C E F (BimoduleCategory.underlying A C E Q)
      (BimoduleCategory.underlying A E F R) hQ hR))
    (isoWhiskerRight (composeWithAssociatorIso A B C E F Q R) (bimoduleToDerived A B F))

lemma derivedAssociatorIso_hom_app (P : BimoduleCategory A B C) :
    (derivedAssociatorIso A B C E F Q R hQ hR).hom.app ((bimoduleToDerived A B C).obj P) =
      (eqToIso (derivedComposeWithPair_fac A B C E F Q R hQ hR)).hom.app P ≫
        (bimoduleToDerived A B F).map
          (associatorIso A B C E F (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)).hom ≫
        (derivedComposeWithComputation A B C F (BimoduleCategory.of A C F (compose A C E F
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)))
          (Bimodule.rightRelativeKFlat_compose A C E F (BimoduleCategory.underlying A C E Q)
      (BimoduleCategory.underlying A E F R) hQ hR) P).inv :=
  Localization.liftNatTrans_app (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    ((composeWith A B C E Q ⋙ composeWith A B E F R) ⋙ bimoduleToDerived A B F)
    (composeWith A B C F (BimoduleCategory.of A C F (compose A C E F
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R))) ⋙
      bimoduleToDerived A B F)
    (derivedComposeWith A B C E Q hQ ⋙ derivedComposeWith A B E F R hR)
    (derivedComposeWith A B C F (BimoduleCategory.of A C F (compose A C E F
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)))
      (Bimodule.rightRelativeKFlat_compose A C E F (BimoduleCategory.underlying A C E Q)
      (BimoduleCategory.underlying A E F R) hQ hR))
    (isoWhiskerRight (composeWithAssociatorIso A B C E F Q R) (bimoduleToDerived A B F)).hom P

end SerrePositivity.DifferentialGraded.BimoduleTensor
