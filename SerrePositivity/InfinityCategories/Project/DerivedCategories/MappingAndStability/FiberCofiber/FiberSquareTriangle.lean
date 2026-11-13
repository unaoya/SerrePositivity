module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.FiberSquareMaps
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.FiberTriangle
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # 指定された四辺による fiber 三角形

概要：引き戻し四角形の下辺・左辺の対と、右辺・上辺の差から distinguished triangle を作る。
方針：二射影による比較式を直和の普遍性で合わせ、D4 の擬同型で標準三角形を移す。
規約：第二射は右辺 − 上辺。使われ方：D6a の長完全列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded Pretriangulated
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]
variable (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)

private lemma mapped_biprod_ext {V W : Type*} [Category V] [Preadditive V]
    [Category W] [Preadditive W] (G : V ⥤ W) [G.Additive]
    {B C : V} [HasBinaryBiproduct B C] {X : W}
    (a b : X ⟶ G.obj (B ⊞ C))
    (h₁ : a ≫ G.map biprod.fst = b ≫ G.map biprod.fst)
    (h₂ : a ≫ G.map biprod.snd = b ≫ G.map biprod.snd) : a = b := by
  have ht : G.map (biprod.fst : B ⊞ C ⟶ B) ≫ G.map biprod.inl +
      G.map (biprod.snd : B ⊞ C ⟶ C) ≫ G.map biprod.inr = 𝟙 _ := by
    rw [← G.map_comp, ← G.map_comp, ← G.map_add, biprod.total, G.map_id]
  calc
    a = a ≫ (G.map biprod.fst ≫ G.map biprod.inl + G.map biprod.snd ≫ G.map biprod.inr) := by
      rw [ht, Category.comp_id]
    _ = b ≫ (G.map biprod.fst ≫ G.map biprod.inl + G.map biprod.snd ≫ G.map biprod.inr) := by
      simp only [Preadditive.comp_add, ← Category.assoc, h₁, h₂]
    _ = b := by rw [ht, Category.comp_id]

/-- 概要：四角形の始点から二つの中間頂点の直和への指定射。
方針：正規化した下辺と左辺の対を取る。
規約：成分の順は下辺、左辺。使われ方：fiber 列の第一射。 -/
def derivedSquarePairMap : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareCornerComplex F ⟶
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftObj ⊞ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightObj :=
  biprod.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomMap F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftMap F)

/-- 概要：標準 fiber 比較と fiber 射影の合成は指定二辺の対にホモトピックである。
方針：直和の二射影で既存の二つの比較式へ帰着する。
規約：ホモトピー圏での等式。使われ方：第一射を指定辺へ置換する。 -/
lemma derivedSquareFiberComparison_pair :
    (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap)) =
      (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map (derivedSquarePairMap F) := by
  let Q := _root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)
  apply mapped_biprod_ext Q
  · rw [← Q.map_comp, ← Q.map_comp, Category.assoc]
    change Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB _ _) =
      Q.map (derivedSquarePairMap F ≫ biprod.fst)
    rw [derivedSquarePairMap, biprod.lift_fst]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison_bottom F
  · rw [← Q.map_comp, ← Q.map_comp, Category.assoc]
    change Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC _ _) =
      Q.map (derivedSquarePairMap F ≫ biprod.snd)
    rw [derivedSquarePairMap, biprod.lift_snd]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison_left F

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

private lemma map_Q_eq_of_quotient_eq {K L : _root_.SerrePositivity.DifferentialGraded.Complex S} (f g : K ⟶ L)
    (h : (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map f =
      (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map g) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g := by
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso (ModuleCat S)).hom.app K)).1
  rw [← (DerivedCategory.quotientCompQhIso (ModuleCat S)).hom.naturality f,
    ← (DerivedCategory.quotientCompQhIso (ModuleCat S)).hom.naturality g]
  exact congrArg (fun k => DerivedCategory.Qh.map k ≫
    (DerivedCategory.quotientCompQhIso (ModuleCat S)).hom.app L) h

/-- 概要：導来圏でも比較射と射影の合成は指定された二辺の対である。
方針：複体ホモトピー圏の等式を導来局所化へ写す。
規約：指定二辺を変更しない。使われ方：distinguished triangle の第一射の同定。 -/
lemma derivedSquareFiberComparison_pair_derived :
    DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap)) =
      DerivedCategory.Q.map (derivedSquarePairMap F) := by
  apply map_Q_eq_of_quotient_eq
  exact derivedSquareFiberComparison_pair F

/-- 概要：指定四辺の対・差からなる導来圏の三角形。
方針：D4 の比較射で接続射を引き戻し、第一射には元の二辺の対を置く。
規約：第二射は右辺 − 上辺、追加の整合性前提はない。使われ方：D6a の接続準同型。 -/
def derivedSquareFiberTriangle (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) :
    Triangle (DerivedCategory (ModuleCat S)) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison_quasiIso F hF
  exact Triangle.mk (DerivedCategory.Q.map (derivedSquarePairMap F))
    (DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberComparisonDerivedTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison F)).mor₃)

/-- 概要：指定された四辺の fiber 三角形は distinguished である。
方針：D4 の比較射による標準三角形の第一射を、二辺の対の等しい導来射へ置き換える。
規約：IsPullbackSquare F だけを前提にする。使われ方：全次数の長完全列。 -/
theorem derivedSquareFiberTriangle_distinguished (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) :
    derivedSquareFiberTriangle F hF ∈ distTriang (DerivedCategory (ModuleCat S)) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison_quasiIso F hF
  change Triangle.mk (DerivedCategory.Q.map (derivedSquarePairMap F)) _ _ ∈ distTriang _
  rw [← derivedSquareFiberComparison_pair_derived]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberComparisonDerivedTriangle_distinguished _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
