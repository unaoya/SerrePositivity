module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorComponents

/-!
概要：底上の fiber ごとの関手の族を、元の全空間上の一つの図式へ降ろす。
方針：全単体の密度表示を保存関手 F で写し、回収した成分を余極限から貼る。
規約：F の通常の余極限保存を使う。cocartesian fibration 性はまだ仮定しない。
使われ方：Kerodon Lemma 7.3.4.5（Tag 02ZR） の族の持ち上げと元の図式の持ち上げの同定。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：回収した局所図式は全単体の図式の cocone を作る。
方針：各成分を脚とし、面・退化による自然性を使う。
規約：元の族の底への射を全ての脚で固定する。
使われ方：大域的な図式への余極限による降下。 -/
def fiberwiseFunctorComponentCocone {B A D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor F D) :
    Cocone (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.simplexDiagram (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D) ⋙ F) where
  pt := D
  ι :=
    { app j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorComponent F f (SSet.yonedaEquiv.symm j.unop.val)
      naturality j k α := by
        change F.map ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.simplexDiagram (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)).map α) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorComponent F f (SSet.yonedaEquiv.symm k.unop.val) = _
        have hw : stdSimplex.map α.unop.hom.unop ≫ SSet.yonedaEquiv.symm k.unop.val =
            SSet.yonedaEquiv.symm j.unop.val := by
          rw [SSet.yonedaEquiv_symm_naturality_left]
          exact congrArg SSet.yonedaEquiv.symm α.unop.map_val
        have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorComponent_naturality F f
          (SSet.yonedaEquiv.symm k.unop.val) (SSet.yonedaEquiv.symm j.unop.val)
          α.unop.hom.unop hw
        change F.map (Over.homMk (stdSimplex.map α.unop.hom.unop) (by
            dsimp only [Over.mk_hom]
            exact (Category.assoc _ _ _).symm.trans
              (congrArg (fun q ↦ q ≫ (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)) hw)) :
            Over.mk (SSet.yonedaEquiv.symm j.unop.val ≫
              (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)) ⟶
            Over.mk (SSet.yonedaEquiv.symm k.unop.val ≫
              (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorComponent F f (SSet.yonedaEquiv.symm k.unop.val) =
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorComponent F f (SSet.yonedaEquiv.symm j.unop.val) ≫ 𝟙 D
        exact hn.trans (Category.comp_id _).symm }

/-- 概要：局所形の余極限を保つ F について、族を大域的な図式へ戻す。
方針：全単体の図式の余極限から成分 cocone へ降ろす。
規約：底は元の族と射影の合成。
使われ方：組み立てた fiber ごとの関手を実際の全空間上の図式へ変える。 -/
def fiberwiseFunctorUncurry {B A D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor F D)
    [PreservesColimitsOfShape A.Elementsᵒᵖ F] :
    F.obj (Over.mk (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)) ⟶ D :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.simplexCocone_map_isColimit F (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)).desc
    (fiberwiseFunctorComponentCocone F f)

/-- 概要：大域図式を任意の単体へ制限すると回収した局所図式に一致する。
方針：余極限の降下の脚に対する計算則。
規約：全次元・退化単体を含む。
使われ方：族と実際の全空間上の図式の往復の検証。 -/
lemma fiberwiseFunctorUncurry_fac {B A D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor F D) [PreservesColimitsOfShape A.Elementsᵒᵖ F]
    {n : SimplexCategory} (σ : stdSimplex.obj n ⟶ A) :
    F.map (Over.homMk σ rfl :
        Over.mk (σ ≫ (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)) ⟶
          Over.mk (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)) ≫
        fiberwiseFunctorUncurry F f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorComponent F f σ := by
  generalize hx : SSet.yonedaEquiv σ = x
  have hs : σ = SSet.yonedaEquiv.symm x := by
    rw [← hx, Equiv.symm_apply_apply]
  subst σ
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.simplexCocone_map_isColimit F (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)).fac
    (fiberwiseFunctorComponentCocone F f)
    (Opposite.op (A.elementsMk (Opposite.op n) x))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
