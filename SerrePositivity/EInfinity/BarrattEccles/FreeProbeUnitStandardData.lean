module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeUnderlyingReplacementComponent
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeUnitIntervalMap
/-!
概要：標準導来単位の任意頂点を、同じ元の自由 probe と cofibrant 標的へ比較する。
方針：既存の頂点表示と元の単位の端点整合を使う。
規約：標準単位と既存の頂点表示を選び直さない。
使われ方：標準単位比較自身を元の弱な全屋根族で検査する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：元の標準単位が使う同じ半自由表示の底の複体。
方針：既存の頂点表示の同じ値を取る。
規約：新しい置換を選ばない。使われ方：標準単位の全要素パラメータ。 -/
abbrev freeProbeUnitComplex (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) : Complex A :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv A x).val

/-- 概要：同じ元の probe 頂点と標準単位の実始域頂点との同型。
方針：既存の probe 比較と既存の半自由頂点表示を合成する。
規約：元の両比較を保持。使われ方：標準単位基準族の始域輸送。 -/
def freeProbeUnitSourceIso (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((ComplexLimits.framedLimitProbeFunctor A).obj (freeProbeUnitComplex A x)))) x :=
  complexProbeDerivedSourceVertexIso A (freeProbeUnitComplex A x) ≪≫
    derivedFreeProbeSourceIso A x

/-- 概要：既存 CAlg_R 頂点の同じ cofibrant 相対圏での表示。
方針：既存の頂点同値の逆の対象を取る。
規約：新しい代数を選ばない。使われ方：標準単位の標的の元の全屋根族。 -/
def freeProbeUnitCofibrantTarget (y : (CAlg_R A) _⦋0⦌) : CofibrantAlgebra A :=
  ULiftHom.objDown.{u + 1, u + 1} ((cAlgVertexEquiv A).symm y)

/-- 概要：同じ cofibrant 表示の局所化源頂点と元の標的との同型。
方針：既存の局所化源比較と同じ頂点表示の逆則を使う。
規約：元の標的を保持。使われ方：標準単位の全族の標的輸送。 -/
def freeProbeUnitTargetIso (y : (CAlg_R A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} (freeProbeUnitCofibrantTarget A y)))) y :=
  cAlgLocalizationSource_vertexIso A
    (ULiftHom.objUp.{u + 1, u + 1} (freeProbeUnitCofibrantTarget A y)) ≪≫
      eqToIso (congrArg HomotopyCategory.mk ((cAlgVertexEquiv A).apply_symm_apply y))

private lemma standardUnitTriangleOfData {C : Type*} [Category* C]
    {a b c d e : C} (p : a ≅ b) (q : b ≅ c) (v : b ⟶ d) (w : d ⟶ e)
    (n : a ⟶ e) (s : a ≅ c) (η : c ⟶ d)
    (hs : s = p ≪≫ q) (hη : η = q.inv ≫ v) (h : p.hom ≫ v ≫ w = n) :
    s.hom ≫ η ≫ w = n := by
  rw [hs, hη]
  simpa only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc] using h

private lemma unitSourceIso_def (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    freeProbeUnitSourceIso A x =
      complexProbeDerivedSourceVertexIso A (freeProbeUnitComplex A x) ≪≫
        derivedFreeProbeSourceIso A x := rfl

private lemma standardUnitHom_def (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    derivedFreeProbeUnitHom A x =
      (derivedFreeProbeSourceIso A x).inv ≫
        freeProbeDerivedUnitComponent A (freeProbeUnitComplex A x) := rfl

/-- 概要：標準単位は同じ両端同型による元の局所化源単位の輸送と整合する。
方針：既存の標準単位の定義と元の単位成分の端点三角形を接続する。
規約：同じ標準単位自身。使われ方：標準単位比較の全族三角形。 -/
lemma freeProbeUnitStandard_triangle (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    (freeProbeUnitSourceIso A x).hom ≫ derivedFreeProbeUnitHom A x ≫
      (hoFunctor.map (cAlgForgetDerived A)).toFunctor.map
        (freeProbeRelativeChosenSourceIso A (freeProbeUnitComplex A x)).hom =
    freeProbeRelativeUnitHom A (freeProbeUnitComplex A x) := by
  exact standardUnitTriangleOfData
    (complexProbeDerivedSourceVertexIso A (freeProbeUnitComplex A x))
    (derivedFreeProbeSourceIso A x)
    (freeProbeDerivedUnitComponent A (freeProbeUnitComplex A x))
    ((hoFunctor.map (cAlgForgetDerived A)).toFunctor.map
      (freeProbeRelativeChosenSourceIso A (freeProbeUnitComplex A x)).hom)
    (freeProbeRelativeUnitHom A (freeProbeUnitComplex A x)) (freeProbeUnitSourceIso A x)
    (derivedFreeProbeUnitHom A x) (unitSourceIso_def A x) (standardUnitHom_def A x)
    (freeProbeRelativeChosenSourceIso_unit_triangle A (freeProbeUnitComplex A x))

end SerrePositivity.EInfinity.BarrattEccles
