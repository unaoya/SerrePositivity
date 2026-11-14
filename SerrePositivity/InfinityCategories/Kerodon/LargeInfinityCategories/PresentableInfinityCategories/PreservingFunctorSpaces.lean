module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.EquivalenceSmallLimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreProduct

/-!
概要：presentable 圏の対象と、Pr^L・Pr^R の関手圏・写像空間を定義する。
方針：元の全関手圏の全部分圏に保存条件を課し、その core を写像空間にする。
規約：右側には accessibility と小極限保存を明示し、随伴関手定理を定義に使わない。
使われ方：Pr^L・Pr^R の豊穣合成と双対性を構成する入力。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の presentable 圏を保持する束縛対象。
方針：単体集合と充填性・presentable 性をまとめる。
規約：単体は u+1、presentable 性の小さい添字は u。
使われ方：Pr^L と Pr^R に共通の対象。 -/
structure PresentableInfinityObject where
  obj : SSet.{u + 1}
  isQuasicategory : Quasicategory obj
  isPresentable : @_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable obj isQuasicategory

attribute [instance] PresentableInfinityObject.isQuasicategory

/-- 概要：小余極限を保つ全関手の元の全部分 ∞ 圏。
方針：全関手圏の頂点を保存条件で制限する。
規約：全ての関手自然変換を保持する。
使われ方：Pr^L の Hom の core を作る。 -/
def PrLFunctorSpace (C D : PresentableInfinityObject.{u}) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom C.obj).obj D.obj)
    (fun v ↦ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj D.obj).symm v))

/-- 概要：accessible かつ小極限を保つ全関手の元の全部分 ∞ 圏。
方針：二つの保存条件を同じ全関手に課す。
規約：右随伴の存在を定義の入力にしない。
使われ方：Pr^R の Hom の core を作る。 -/
def PrRFunctorSpace (C D : PresentableInfinityObject.{u}) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom C.obj).obj D.obj)
    (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj D.obj).symm v) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj D.obj).symm v))

instance prLFunctorSpace_quasicategory (C D : PresentableInfinityObject.{u}) :
    Quasicategory (PrLFunctorSpace C D) := by
  dsimp [PrLFunctorSpace]
  infer_instance

instance prRFunctorSpace_quasicategory (C D : PresentableInfinityObject.{u}) :
    Quasicategory (PrRFunctorSpace C D) := by
  dsimp [PrRFunctorSpace]
  infer_instance

/-- 概要：Pr^L の元の関手同値と全高次単体を持つ写像空間。
方針：保存関手圏の core を取る。
規約：関手の同型類の集合へは商にしない。
使われ方：Pr^L の単体的豊穣 Hom。 -/
def PrLMappingSpace (C D : PresentableInfinityObject.{u}) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (PrLFunctorSpace C D)

/-- 概要：Pr^R の元の関手同値と全高次単体を持つ写像空間。
方針：accessible な極限保存関手圏の core を取る。
規約：同じ対象の全関手圏を使う。
使われ方：Pr^R の単体的豊穣 Hom。 -/
def PrRMappingSpace (C D : PresentableInfinityObject.{u}) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (PrRFunctorSpace C D)

instance prLMappingSpace_kanComplex (C D : PresentableInfinityObject.{u}) :
    KanComplex (PrLMappingSpace C D) := by
  dsimp [PrLMappingSpace]
  infer_instance

instance prRMappingSpace_kanComplex (C D : PresentableInfinityObject.{u}) :
    KanComplex (PrRMappingSpace C D) := by
  dsimp [PrRMappingSpace]
  infer_instance

/-- 概要：小余極限保存は関手の合成で閉じる。
方針：元の指定全余錐を順に写す。
規約：小さい形状と全余錐を保持する。
使われ方：Pr^L の合成。 -/
lemma PreservesSmallColimits.comp {C D E : SSet.{u + 1}} {F : C ⟶ D} {G : D ⟶ E}
    (hF : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits F) (hG : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits G) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (F ≫ G) := by
  intro K a c hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc c.val F G).symm).mpr
    (hG K _ _ (hF K a c hc))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservesSmallColimits (comp)


/-- 概要：小極限保存は関手の合成で閉じる。
方針：同じ全錐を順に写す。
規約：図式の充填性を要求しない。
使われ方：Pr^R の合成。 -/
lemma PreservesSmallLimits.comp {C D E : SSet.{u + 1}} {F : C ⟶ D} {G : D ⟶ E}
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits F) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits (F ≫ G) := by
  intro K a c hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _ (Category.assoc c.val F G).symm).mpr
    (hG K _ _ (hF K a c hc))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservesSmallLimits (comp)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.2.6.1" (partial := stronger-hyp) "仮定：C,D が presentable（Lean が強い：原典の任意の準圏にこの仮定を追加）。結論：左右随伴の存在で頂点を選ぶ FunL(C,D),FunR(C,D) の全部分準圏（この場合に一致）。PrL は全小余極限保存、PrR は accessible かつ全小極限保存で定義され、二つの存在判定の同値により同じ頂点条件となる。core だけには制限していない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace
attribute [cite HTT "5.2.6.1" (partial := stronger-hyp) "仮定：C,D が presentable（Lean が強い：原典の任意の準圏にこの仮定を追加）。結論：左右随伴の存在で頂点を選ぶ FunL(C,D),FunR(C,D) の全部分準圏（この場合に一致）。PrL は全小余極限保存、PrR は accessible かつ全小極限保存で定義され、二つの存在判定の同値により同じ頂点条件となる。core だけには制限していない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace
attribute [cite HTT "5.5.3.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace
attribute [cite HTT "5.5.3.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace
attribute [cite HTT "5.5.3.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject
attribute [cite HTT "6.3.1.4" (partial := stronger-hyp) "仮定：二つの幾何学的射とその左随伴（Lean が強い：左随伴が有限極限だけでなく全小極限を保存すると仮定）。結論：同じ左随伴の合成は全小極限を保存し、逆順の右随伴の合成と実際の ∞ 随伴を成すため、この場合の幾何学的射の合成は一致。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservesSmallLimits.comp
