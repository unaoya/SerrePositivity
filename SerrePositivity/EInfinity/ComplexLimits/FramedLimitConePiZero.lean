module

public import SerrePositivity.EInfinity.ComplexLimits.SourceRightConeNaturality
public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramPiZero

/-!
# 実際の右 frame の錐の π₀ と定値図式からの局所化 Hom

概要：BM 命題 4.1・Hovey §5.4 の右 frame の錐で元の定値図式からの導来 Hom を計算する。
方針：両 frame の錐比較と始域 frame の π₀ 比較を合成し、試験始域の置換を消す。
規約：具体的な図式モデルの普通の局所化を使い、元の複体の cofibrancy は不要。
使われ方：実際の homotopy 極限の計算対象の導来普遍性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：試験始域の定値図式は元の定値図式と局所化後に同型（Hovey §5）。
方針：元の試験始域の擬同型を各値で確認して反転する。
規約：元の同じ置換射を定値図式へ送る。
使われ方：右 frame の錐の Hom 比較から置換始域を消す。 -/
def constantProbeLocalizedIso (Y : (Complex A)) :
    let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ (Complex A))).Q
    Q.obj ((Functor.const K).obj (framedLimitProbe A Y)) ≅ Q.obj ((Functor.const K).obj Y) := by
  let := projectiveModelCategory A
  let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  let Q := (weakEquivalences (K ⥤ (Complex A))).Q
  let p := (Functor.const K).map (framedLimitProbeComparison A Y)
  have hp : weakEquivalences (K ⥤ (Complex A)) p :=
    ((BarrattEccles.CarrierDiagram.weakEquivalence_iff A K p).mpr
      (fun _ => framedLimitProbeComparison_quasiIso A Y)).mem
  have : IsIso (Q.map p) := Localization.inverts Q
    (weakEquivalences (K ⥤ (Complex A))) p hp
  exact asIso (Q.map p)

/-- 概要：右 frame の錐の π₀ は元の定値図式からの局所化 Hom（Hovey §5.4）。
方針：同じ試験始域の始域 frame の錐へ戻し、二つの局所化同型を使う。
規約：元の Y と元の F をそのまま局所化し、追加の cofibrancy 条件はない。
使われ方：一般 homotopy 極限の具体的な計算対象との導来随伴。 -/
def framedLimitConePiZeroEquiv (Y : (Complex A)) (F : K ⥤ (Complex A)) :
    let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ (Complex A))).Q
    SSet.π₀ ((framedLimitConeSpace A K Y).obj F) ≃
      (Q.obj ((Functor.const K).obj Y) ⟶ Q.obj F) := by
  let := projectiveModelCategory A
  let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  exact (sourceRightConeComparisonIso A K Y F SSet.π₀Functor
    SimplicialModel.PiZeroLocalization.inverts_anodyne).toEquiv.symm.trans
      ((BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv A K (framedLimitProbe A Y)
        F).trans
        (Iso.homCongr (constantProbeLocalizedIso A K Y) (Iso.refl _)))

/-- 概要：右 frame の錐の π₀ と定値図式の Hom の比較は終域に自然（Hovey §5.4）。
方針：同じ両錐比較の逆の自然性と始域 frame の Hom 比較の自然性を合成する。
規約：後合成は元の図式射の同じ局所化像。
使われ方：具体的な計算対象の導来随伴の終域自然性。 -/
lemma framedLimitConePiZeroEquiv_target (Y : (Complex A))
    {F G : K ⥤ (Complex A)} (g : F ⟶ G)
    (z : SSet.π₀ ((framedLimitConeSpace A K Y).obj F)) :
    let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ (Complex A))).Q
    framedLimitConePiZeroEquiv A K Y G
        (SSet.mapπ₀ ((framedLimitConeSpace A K Y).map g) z) =
      framedLimitConePiZeroEquiv A K Y F z ≫ Q.map g := by
  let := projectiveModelCategory A
  let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  let Q := (weakEquivalences (K ⥤ (Complex A))).Q
  let e := sourceRightConeComparisonNatIso A K Y SSet.π₀Functor
    SimplicialModel.PiZeroLocalization.inverts_anodyne
  have hn : (e.app G).inv (SSet.mapπ₀ ((framedLimitConeSpace A K Y).map g) z) =
      SSet.mapπ₀ ((BarrattEccles.CarrierDiagram.constantDiagramSourceHom A K (framedLimitProbe A
        Y)).map g)
        ((e.app F).inv z) := ConcreteCategory.congr_hom (e.inv.naturality g) z
  change (constantProbeLocalizedIso A K Y).inv ≫
      BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv A K (framedLimitProbe A Y) G
        ((e.app G).inv (SSet.mapπ₀ ((framedLimitConeSpace A K Y).map g) z)) ≫ 𝟙 _ =
    ((constantProbeLocalizedIso A K Y).inv ≫
      BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv A K (framedLimitProbe A Y) F
        ((e.app F).inv z) ≫ 𝟙 _) ≫
        Q.map g
  rw [hn, BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv_target]
  simp only [Category.comp_id, Category.assoc]
  rfl

end SerrePositivity.EInfinity.ComplexLimits
