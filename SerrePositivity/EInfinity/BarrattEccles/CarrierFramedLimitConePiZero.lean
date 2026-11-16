module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierSourceRightConeNaturality
public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramPiZero

/-!
# 底の右錐の π₀ と元の定値複体図式からの局所化 Hom

概要：BM 命題 4.1・Hovey §5.4 の底の両 frame の錐から定値図式の Hom を計算する。
方針：混合 Hom の錐比較と複体図式の π₀ 比較を合成し、試験始域の置換を消す。
規約：任意の元の複体を使い、元の E 代数図式を同じ忘却で送る。
使われ方：一般 homotopy 極限の忘却後の Hom の普遍性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：複体の試験始域の定値図式比較は局所化後に同型（Hovey §5.4）。
方針：元の比較の擬同型性を各頂点で反転する。
規約：元の同じ関手的試験始域と比較を使う。
使われ方：底の右錐の Hom 比較から試験始域を消す。 -/
def carrierConstantProbeLocalizedIso (Y : Complex A) :
    let := CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ Complex A)).Q
    Q.obj ((Functor.const K).obj (carrierFramedLimitProbe A Y)) ≅
      Q.obj ((Functor.const K).obj Y) := by
  let := CarrierDiagram.projectiveModelCategory A K
  let Q := (weakEquivalences (K ⥤ Complex A)).Q
  let p := (Functor.const K).map ((carrierFramedLimitProbeComparison A).app Y)
  have hp : weakEquivalences (K ⥤ Complex A) p :=
    ((CarrierDiagram.weakEquivalence_iff A K p).mpr
      (fun _ => carrierFramedLimitProbeComparison_quasiIso A Y)).mem
  have : IsIso (Q.map p) := Localization.inverts Q (weakEquivalences (K ⥤ Complex A)) p hp
  exact asIso (Q.map p)

/-- 概要：底の右錐の π₀ は元の定値複体図式からの局所化 Hom（Hovey §5.4）。
方針：同じ試験始域の始域錐へ戻し、既存の π₀ 比較と局所化同型を合成する。
規約：元の複体・図式・右錐を保持し、追加の cofibrancy は不要。
使われ方：忘却後の計算対象の Hom の普遍性の片側。 -/
def carrierFramedLimitConePiZeroEquiv (Y : Complex A) (F : K ⥤ (operad A).Algebra) :
    let := CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ Complex A)).Q
    SSet.π₀ ((carrierFramedLimitConeSpace A K Y).obj F) ≃
      (Q.obj ((Functor.const K).obj Y) ⟶ Q.obj ((Diagram.forget A K).obj F)) := by
  let := CarrierDiagram.projectiveModelCategory A K
  exact (carrierSourceRightConeComparisonIso A K Y F SSet.π₀Functor
    SimplicialModel.PiZeroLocalization.inverts_anodyne).toEquiv.symm.trans
      ((CarrierDiagram.constantDiagramSourcePiZeroEquiv A K (carrierFramedLimitProbe A Y)
        ((Diagram.forget A K).obj F)).trans
        (Iso.homCongr (carrierConstantProbeLocalizedIso A K Y) (Iso.refl _)))

/-- 概要：底の右錐と定値図式の Hom の比較は元の図式射に自然（Hovey §5.4）。
方針：同じ両錐比較の逆の自然性と始域側の π₀ 比較の自然性を合成する。
規約：後合成は元の図式射を忘却して局所化したもの。
使われ方：一般 homotopy 極限の忘却後の導来 Hom 比較。 -/
lemma carrierFramedLimitConePiZeroEquiv_target (Y : Complex A)
    {F G : K ⥤ (operad A).Algebra} (g : F ⟶ G)
    (z : SSet.π₀ ((carrierFramedLimitConeSpace A K Y).obj F)) :
    let := CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ Complex A)).Q
    carrierFramedLimitConePiZeroEquiv A K Y G
        (SSet.mapπ₀ ((carrierFramedLimitConeSpace A K Y).map g) z) =
      carrierFramedLimitConePiZeroEquiv A K Y F z ≫ Q.map ((Diagram.forget A K).map g) := by
  let := CarrierDiagram.projectiveModelCategory A K
  let Q := (weakEquivalences (K ⥤ Complex A)).Q
  let e := carrierSourceRightConeComparisonNatIso A K Y SSet.π₀Functor
    SimplicialModel.PiZeroLocalization.inverts_anodyne
  have hn : (e.app G).inv (SSet.mapπ₀ ((carrierFramedLimitConeSpace A K Y).map g) z) =
      SSet.mapπ₀ ((CarrierDiagram.constantDiagramSourceHom A K
        (carrierFramedLimitProbe A Y)).map ((Diagram.forget A K).map g)) ((e.app F).inv z) :=
    ConcreteCategory.congr_hom (e.inv.naturality g) z
  change (carrierConstantProbeLocalizedIso A K Y).inv ≫
      CarrierDiagram.constantDiagramSourcePiZeroEquiv A K (carrierFramedLimitProbe A Y)
        ((Diagram.forget A K).obj G)
        ((e.app G).inv (SSet.mapπ₀ ((carrierFramedLimitConeSpace A K Y).map g) z)) ≫ 𝟙 _ =
    ((carrierConstantProbeLocalizedIso A K Y).inv ≫
      CarrierDiagram.constantDiagramSourcePiZeroEquiv A K (carrierFramedLimitProbe A Y)
        ((Diagram.forget A K).obj F) ((e.app F).inv z) ≫ 𝟙 _) ≫
          Q.map ((Diagram.forget A K).map g)
  rw [hn, CarrierDiagram.constantDiagramSourcePiZeroEquiv_target]
  simp only [Category.comp_id, Category.assoc]
  rfl

/-- 概要：忘却後の定値図式と元の計算対象の底への導来 Hom は同値（Hovey §5.4）。
方針：同じ底の右錐の π₀ を通る二つの同値を合成する。
規約：任意の複体を始域に使い、元の計算対象の底を保持する。
使われ方：一般 homotopy 極限の忘却後の普遍性と右導来比較。 -/
def carrierFramedLimitDerivedHomEquiv (Y : Complex A) (F : K ⥤ (operad A).Algebra) :
    let := projectiveModelCategory A
    let := CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    let QD := (weakEquivalences (K ⥤ Complex A)).Q
    (QD.obj ((Functor.const K).obj Y) ⟶ QD.obj ((Diagram.forget A K).obj F)) ≃
      (Q.obj Y ⟶ Q.obj ((framedLimitFunctor A K).obj F).carrier) := by
  let := projectiveModelCategory A
  let := CarrierDiagram.projectiveModelCategory A K
  exact (carrierFramedLimitConePiZeroEquiv A K Y F).symm.trans
    (carrierFramedLimitHomPiZeroEquiv A K F Y)

end SerrePositivity.EInfinity.BarrattEccles
