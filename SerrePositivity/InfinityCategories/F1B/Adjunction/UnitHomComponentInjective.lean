module

public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFamilyComparisonBijective
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantHomFaithful

/-!
概要：各点の単位比較条件からホモトピー圏の単位 Hom 比較の単射性を得る。
方針：定値関手間の比較の全単射性を、零単体パラメータでの評価によって検出する。
規約：h Fun 全体の等式を各点だけで判定するとは主張しない。
使われ方：B1 の左 zigzag の各点の一意性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：定値の二胞体に対する単位比較は、各点の単位 Hom 比較の定値化。
方針：前後合成の公式と定値二胞体の合成保存を使う。
規約：パラメータ A は quasicategory。
使われ方：各点の Hom 単射性への移行。 -/
lemma constantUnitHomMap_constant {A X Y : SSet.{u}} [Quasicategory A]
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (α : (HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) x) : hoFunctor.obj Y) ⟶
      HomotopyCategory.mk y) :
    constantUnitHomMap η A x y (constantFunctorHomMap A α) =
      constantFunctorHomMap A (qcatUnitComponent η x ≫ (hoFunctor.map G).toFunctor.map α) := by
  rw [constantUnitHomMap_formula,
    constantFunctorHomMap_postcomp, constantFunctorHomMap_comp]

/-- 概要：各点の標準単位比較の同値性はホモトピー圏の単位 Hom 比較を単射にする。
方針：零単体パラメータで定値関手の単位比較に移し、二つの単射性を使う。
規約：結論は hY の Hom に限る。自然変換全体の忠実性とは混同しない。
使われ方：左三角恒等式の各点での一意性。 -/
lemma UnitMappingSpaceCondition.unitComponentHomMap_injective
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : FunctorHom (𝟙 X) (F ≫ G)}
    (hη : UnitMappingSpaceCondition η) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    Function.Injective (fun α :
      (HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) x) : hoFunctor.obj Y) ⟶
        HomotopyCategory.mk y ↦ qcatUnitComponent η x ≫ (hoFunctor.map G).toFunctor.map α) := by
  intro α β h
  apply constantFunctorHomMap_injective (A := (Δ[0] : SSet.{u}))
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) _ _
  apply (hη.constantUnitHomMap_bijective (A := (Δ[0] : SSet.{u})) x y).1
  rw [constantUnitHomMap_constant, constantUnitHomMap_constant]
  exact congrArg (constantFunctorHomMap (Δ[0] : SSet.{u})) h

/-- 概要：定値の始域・標的に対する単位 Hom 比較は単射。
方針：両端の定値関手の輸送を付けて、定値単位比較の単射性に戻す。
規約：関手の端点は定値に限定する。
使われ方：左 zigzag の各頂点への制限を恒等と比較する。 -/
lemma UnitMappingSpaceCondition.qcatUnitHomMap_constant_injective
    {A X Y : SSet.{u}} [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : FunctorHom (𝟙 X) (F ≫ G)}
    (hη : UnitMappingSpaceCondition η) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    Function.Injective (qcatUnitHomMap η (SSet.const x : A ⟶ X) (SSet.const y)) := by
  intro α β h
  have hh := congrArg (fun k ↦ k ≫ (constantFunctorCompIso A y G).hom) h
  have hc : constantUnitHomMap η A x y ((constantFunctorCompIso A x F).inv ≫ α) =
      constantUnitHomMap η A x y ((constantFunctorCompIso A x F).inv ≫ β) := by
    simpa only [constantUnitHomMap, Iso.hom_inv_id_assoc] using hh
  have hi := (hη.constantUnitHomMap_bijective (A := A) x y).1 hc
  exact (cancel_epi (constantFunctorCompIso A x F).inv).1 hi

end SerrePositivity.InfinityCategories
