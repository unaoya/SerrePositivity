module

public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitLocalization
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitHomIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.UnitComparisons.LocalizedAdjunction

/-!
# 定値図式と実際の極限計算関手の局所化圏上の随伴

概要：BM 命題 4.1・Hovey §1.3 の具体的な Hom 同値から局所化圏上の随伴を構成する。
方針：局所化の因子化同型で両辺を移し、両変数の前合成の充満忠実性を使う。
規約：元の計算対象を保持し、モデル圏の元の随伴は仮定しない。
使われ方：具体的な homotopy 極限の右導来普遍性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra


variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：降ろした二つの関手の Hom は元の両変数上で自然に同型（Hovey §1.3）。
方針：同じ導来 Hom 同型の両辺を局所化の因子化自然同型で移す。
規約：対象ごとの輸送も全体の関手同型から構成する。
使われ方：両変数の局所化から Hom 同型を復元する入力。 -/
def framedLimitRestrictedHomIso :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A K
    let Q := (weakEquivalences (operad A).Algebra).Q
    let QD := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.restrict Q QD (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHom (localizedConstantDiagram A K)) ≅
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.restrict Q QD (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightHom (localizedFramedLimit A K)) := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  let Q := (weakEquivalences (operad A).Algebra).Q
  let QD := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
  let P := (Functor.whiskeringLeft (K ⥤ (operad A).Algebra) _ (Type (u + 1))).obj QD
  let c := localizedConstantDiagramComparison A K
  let r := localizedFramedLimitComparison A K
  let eleft : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.restrict Q QD (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHom (localizedConstantDiagram A K)) ≅
      framedLimitRawLeftHom A K :=
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (NatIso.op c.symm) coyoneda) P
  let eright : framedLimitRawRightHom A K ≅
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.restrict Q QD (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightHom (localizedFramedLimit A K)) :=
    Functor.isoWhiskerLeft (Q.op ⋙ coyoneda)
      ((Functor.whiskeringLeft (K ⥤ (operad A).Algebra)
        (weakEquivalences (operad A).Algebra).Localization (Type (u + 1))).mapIso r.symm)
  exact eleft ≪≫ framedLimitRawHomIso A K ≪≫ eright

/-- 概要：定値図式と具体的な計算関手は普通の局所化圏上で随伴（Hovey §1.3）。
方針：元の両変数上の自然な Hom 同型を局所化圏全体へ降ろす。
規約：単体集合モデルや元の始域の cofibrancy は不要。
使われ方：具体的な極限計算の導来普遍性の随伴側の根拠。 -/
def framedLimitAdjunction :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A K
    localizedConstantDiagram A K ⊣ localizedFramedLimit A K := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.descendAdjunction (weakEquivalences (operad A).Algebra).Q
    (weakEquivalences (operad A).Algebra)
    (weakEquivalences (K ⥤ (operad A).Algebra)).Q
    (weakEquivalences (K ⥤ (operad A).Algebra)) (localizedConstantDiagram A K)
    (localizedFramedLimit A K) (framedLimitRestrictedHomIso A K)

/-- 概要：局所化圏上の随伴の Hom 同値は元の導来 Hom 同値を回収（Hovey §1.3）。
方針：二つの充満忠実な前合成の成分計算と因子化同型を評価する。
規約：元の対象の局所化像で同じ Hom 同値を使う。
使われ方：単位・余単位と元の具体的な錐の類の照合。 -/
lemma framedLimitAdjunction_homEquiv (Y : (operad A).Algebra)
    (F : K ⥤ (operad A).Algebra) :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A K
    let Q := (weakEquivalences (operad A).Algebra).Q
    let QD := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
    ∀ x : (localizedConstantDiagram A K).obj (Q.obj Y) ⟶ QD.obj F,
      (framedLimitAdjunction A K).homEquiv (Q.obj Y) (QD.obj F) x =
        framedLimitDerivedHomEquiv A K Y F
            ((localizedConstantDiagramComparison A K).inv.app Y ≫ x) ≫
          (localizedFramedLimitComparison A K).inv.app F := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  dsimp only
  intro x
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.descendAdjunction_homEquiv_app (weakEquivalences (operad A).Algebra).Q
      (weakEquivalences (operad A).Algebra)
      (weakEquivalences (K ⥤ (operad A).Algebra)).Q
      (weakEquivalences (K ⥤ (operad A).Algebra)) (localizedConstantDiagram A K)
      (localizedFramedLimit A K) (framedLimitRestrictedHomIso A K) Y F x

/-- 概要：随伴の同値を元の両対象へ戻すと元の導来 Hom 同値（Hovey §1.3）。
方針：二つの因子化同型の順方向と逆方向を相殺する。
規約：元の局所化射のすべてで同じ Hom 同値を回収する。
使われ方：随伴の類と具体的な錐の類の比較。 -/
lemma framedLimitAdjunction_homEquiv_comparison (Y : (operad A).Algebra)
    (F : K ⥤ (operad A).Algebra) :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A K
    let Q := (weakEquivalences (operad A).Algebra).Q
    let QD := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
    ∀ x : QD.obj ((Functor.const K).obj Y) ⟶ QD.obj F,
      (framedLimitAdjunction A K).homEquiv (Q.obj Y) (QD.obj F)
          ((localizedConstantDiagramComparison A K).hom.app Y ≫ x) ≫
        (localizedFramedLimitComparison A K).hom.app F = framedLimitDerivedHomEquiv A K Y F x := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  dsimp only
  intro x
  have h := framedLimitAdjunction_homEquiv A K Y F
    ((localizedConstantDiagramComparison A K).hom.app Y ≫ x)
  have he := congrArg (fun f => f ≫ (localizedFramedLimitComparison A K).hom.app F) h
  simp only [Iso.inv_hom_id_app_assoc, Category.assoc, Iso.inv_hom_id_app] at he
  exact he.trans (Category.comp_id _)

end SerrePositivity.EInfinity.BarrattEccles
