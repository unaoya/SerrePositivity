module

public import SerrePositivity.InfinityCategories.HomotopyLimits.GeneralReflectedFibers
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeSmallReflectedFiber

/-!
概要：任意の小圏上の coherent な錐から strict な錐への pinched Hom の導来 fiber 模型。
方針：一般の end と切断の同値を既存の fiber 比較へ渡し、追加の比較仮定を除く。
規約：反転比較 q′ の元の宇宙の fiber 全体を ULift する模型を使う。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、A3d による一般の極限判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

local instance generalConeFiberTargetKan (F : I ⥤ C) (x : C) :
    KanComplex (bousfieldKanHolim (simplicialHomDiagram F x ⋙ SSet.opFunctor)) := by
  have : ∀ i, KanComplex ((simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  exact bousfieldKanHolim_kanComplex _

/-- 概要：任意の coherent な錐の標準切断点から回収した元の宇宙の反転 end の点。
方針：一般の end 比較の同値性を使い、標準点を比較の逆で戻す。
規約：追加の比較同値の仮定は不要。選択した逆の像とのずれは既存の path で照合する。
使われ方：Kerodon 7.5.4.6、一般の錐の pinched Hom の導来 fiber の固定点。 -/
def generalStrictConeReflectedEndPoint {F : I ⥤ C}
    (d : JoinCone (strictCoherentDiagram F)) :
    (bousfieldKanHolim
      (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor)) _⦋0⦌ :=
  strictConeSmallReflectedEndPoint d
    (reflectedHomHolimConeComparison_homotopyEquivalence F (coherentNerveObject d.vertex))

/-- 概要：一般の錐から strict な錐への pinched Hom は反転比較 q′ の導来 fiber の ULift と同値。
方針：一般の end 比較の同値性を宇宙を戻した既存の fiber 比較に代入する。
規約：錐 c の極限性や Hom の fibration 性を要求せず、d は全ての coherent な錐を動く。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6、A3d の写像空間による検出への具体的な模型。 -/
def strictConePinched_generalReflectedEnd_equivalence {F : I ⥤ C}
    (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
          (generalStrictConeReflectedEndPoint d))) :=
  strictConePinched_smallReflectedEndDerivedFiberEquivalence c d
    (reflectedHomHolimConeComparison_homotopyEquivalence F (coherentNerveObject d.vertex))

/-- 概要：一般の錐の pinched Hom の可縮性は標準点での反転比較の導来 fiber 模型の可縮性と同値。
方針：構成した実際の quasicategory の同値で可縮 Kan 性を保ち反映する。
規約：可縮性は A3d の全境界の充填で、単なる π₀ の一意性に弱めない。
使われ方：Kerodon 7.5.4.6、一般形状の極限判定への比較の適用。 -/
lemma strictConePinched_isContractibleKan_iff_generalReflectedEnd {F : I ⥤ C}
    (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    IsContractibleKan
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c)) ↔
    IsContractibleKan ((SSet.uliftFunctor.{v, u}).obj
      (comparisonFiber (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
        (generalStrictConeReflectedEndPoint d))) :=
  (strictConePinched_generalReflectedEnd_equivalence c d).isContractibleKan_iff

/-- 概要：任意の strict な錐の native な極限性は全ての錐の標準点の導来 fiber 模型で検出できる。
方針：A3d の全 pinched Hom の可縮性判定を、構成した fiber 模型へ移す。
規約：全ての coherent な錐 d を量化し、strict な錐だけへの制限をしない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6、一般形状の具体的な fiber による判定。 -/
lemma strictCoherentCone_isLimit_iff_generalReflectedEndPointFibers {F : I ⥤ C}
    (c : Cone F) :
    IsLimitCone (strictCoherentCone c) ↔ ∀ d : JoinCone (strictCoherentDiagram F),
      IsContractibleKan ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
          (generalStrictConeReflectedEndPoint d))) := by
  rw [isLimitCone_iff_conePinchedHom_isContractibleKan]
  exact forall_congr' fun d ↦ strictConePinched_isContractibleKan_iff_generalReflectedEnd c d

end
end SerrePositivity.InfinityCategories.HomotopyLimits
